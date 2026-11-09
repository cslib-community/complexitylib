/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.UpperDominationOptimum
public import Complexity.Computability.Complexity.FineGrained.TwoBoundaryWitness
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Returned upper-domination witnesses

Recover a full satisfying word of the actual selection/gate/mark formula using unit-clause
self-reduction, then retain its original selection prefix. All formula wires are linear in the
original vertex count, so fixing auxiliaries as well still uses linearly many feasibility calls.
This realizes the witness clause of [ChenJiangZhu2027], Corollary 7.4 / Appendix D.5 (pp.26,37).

## Main definitions

* `selected`: returned original bits as an ordinary vertex set.
* `solve`: actual optimum pass, unit-clause recovery and original-prefix output.

## Main results

* `model_sound`: pointwise original-set soundness of the actual graph writer.
* `exists_optimalWitness_realEta_certificate`: returned globally optimal minimal dominating set
  with complete sharp native time and global polynomial workspace.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Boolean

/-- The actual original vertex set decoded from the returned Boolean selection word. -/
@[expose] def selected {n : ℕ} (bits : List Bool) : Set (Fin n) :=
  {u | bits.getD u.val false = true}

open Classical in
/-- Pointwise soundness of the actual original-input writer. This applies to the word returned by
unit-clause self-reduction, without treating an existential count bridge as a witness decoder. -/
theorem model_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (y : ℕ → Bool)
    (hB : (TwoBoundary.BinaryFrontend.side (build (ofGraph G k))).eval y = true)
    (hP : ∀ p ∈ TwoBoundary.BinaryFrontend.conditions (build (ofGraph G k)),
      DNF.eval y p = true) :
    Minimal G.IsDominatingSet {u | y u.val = true} ∧
      k ≤ (Nat.card {u : Fin n | y u.val = true} : ℤ) := by
  let c := CardinalityInterval.circuit n k.toNat n
  let a := c.size
  have haux : auxiliary (ofGraph G k) = a :=
    IndependentDominationInterval.auxiliary_ofGraph G k.toNat n
  have hcard : cardinalityInput (ofGraph G k) = (n, k.toNat, n) := rfl
  change (CardinalityInterval.formula (cardinalityInput (ofGraph G k)) ++
    upper (coreInput (ofGraph G k))).eval y = true at hB
  rw [CNF.eval_append, Bool.and_eq_true] at hB
  have hcircuit : c.eval interpretation (fun u => y u.val) = CardinalityInterval.wanted := by
    have hf := hB.1
    rw [hcard, CardinalityInterval.formula, CardinalityInterval.payload_eq] at hf
    exact ((FunctionalCNF.eval_write_iff c CardinalityInterval.wanted
      (fun u => y u.val) y (fun _ => rfl)).mp hf).2
  have hk := (CardinalityInterval.circuit_accepts n k.toNat n (fun u => y u.val)).mp hcircuit
  have hupper : (finiteUpper G a).eval (fun j => y j.val) = true := by
    have hu := hB.2
    change (upper (IndependentDomination.ofGraph G, n + auxiliary (ofGraph G k))).eval y = true
      at hu
    rw [haux, upper_ofGraph, CNF.eval_relabel] at hu
    exact hu
  have hD := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hD
  have hDom : (finiteDomination G a).map (CNF.relabel Fin.val) =
      IndependentDomination.coverage (IndependentDomination.ofGraph G) := by
    rw [hD]
    simp only [finiteDomination, List.map_map, CNF.relabel, Clause.relabel, Function.comp_def]
    rfl
  have hconds : ∀ p ∈ finiteDomination G a ++ finiteWitnesses G a,
      DNF.eval (fun j => y j.val) p = true := by
    change ∀ p ∈ IndependentDomination.coverage (IndependentDomination.ofGraph G) ++
      witnesses (IndependentDomination.ofGraph G, n + auxiliary (ofGraph G k)),
        DNF.eval y p = true at hP
    rw [haux, witnesses_ofGraph, ← hDom, ← List.map_append] at hP
    intro p hp
    have h := hP (CNF.relabel Fin.val p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    change (p.any fun t => t.all fun l => y l.1.val == l.2) = true
    simpa only [DNF.eval, CNF.relabel, Clause.relabel, Term.eval, List.any_map,
      List.all_map, Function.comp_def, Literal.eval, Prod.map, id_eq] using h
  have hm := (finite_semantics G a (fun j => y j.val)).mp ⟨hupper, hconds⟩
  have hmin : Minimal G.IsDominatingSet {u | y u.val = true} :=
    (G.exists_privateMarking_iff _).mp ⟨_, hm⟩
  have hw : Cslib.BitString.weight (fun u : Fin n => y u.val) =
      Nat.card {u : Fin n | y u.val = true} := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  refine ⟨hmin, ?_⟩
  rw [hw] at hk
  exact Int.toNat_le.mp hk.1

open Classical in
/-- Recover the full actual formula word. Only its original selection prefix will be output by
`solve`; fixing auxiliary wires still takes linearly many sharp calls in original vertices. -/
theorem exists_recovery_sharp_certificate :
    ∃ recover : UpperDomination.Input → List Bool,
      ∃ cs : NativeCertificate recover UpperDomination.encInput encBits, ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((UpperDomination.encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
          ((∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)) →
            let bits := recover (ofGraph G k)
            bits.length = (n + (CardinalityInterval.circuit n k.toNat n).size) + n ∧
              Minimal G.IsDominatingSet (selected (n := n) bits) ∧
                k ≤ (Nat.card (selected (n := n) bits) : ℤ)) ∧
          cs.time (ofGraph G k) ≤ C * ((UpperDomination.encInput (ofGraph G k)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_recovery_sharp_certificate 3 1 (by omega)
  let cc := NativeCertificate.ofPolyTime build_polytime
  have hcc := NativeCertificate.ofPolyTime_isPolynomial build_polytime
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    D * ((TwoBoundary.BinaryFrontend.encInput (build x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const D).mul
      ((build_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 2097152))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build, cs, C, e, 38120 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ k
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G k
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := (CardinalityInterval.circuit n k.toNat n).size
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n k.toNat n
  have htime : cp.time (build (ofGraph G k)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (4 * n + a)) := by
    rw [← hbuild, hplen] at ht
    have hh : (n + (CardinalityInterval.circuit n k.toNat n).size + n) + 2 * n =
        4 * n + a := by dsimp only [a]; omega
    simpa only [hh] using ht
  have hscale : Nat.logLogSqrtLogScale (4 * n + a) ≤
      38120 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 2097152 := by
    by_cases hn : 1906 ≤ n
    · have hdim : 4 * n + a ≤ 1906 * n := by omega
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim (by omega : 4 ≤ 1906 * n)
      have hl := Nat.logLogSqrtLogScale_mul_le 1906 (by omega : max 4 1906 ≤ n)
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (by omega : 4 * n + a ≤ 2097152) (by decide : 4 ≤ 2097152)
      omega
  let E := 2 ^ ((38120 * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (4 * n + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (38120 * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale 2097152)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · intro hfeas
    obtain ⟨S, hmin, hk⟩ := hfeas
    obtain ⟨marks, hm⟩ := (G.exists_privateMarking_iff S).mpr hmin
    have hpos : 0 < Fintype.card {p : Set (Fin n) × Set (Fin n) //
        G.IsPrivateMarking p.1 p.2 ∧ k ≤ (Nat.card p.1 : ℤ)} :=
      Fintype.card_pos_iff.mpr ⟨⟨(S, marks), hm, hk⟩⟩
    rw [← word_count_eq_pairs, ← hcount] at hpos
    have hbase : ∃ σ : Fin ((n + (CardinalityInterval.circuit n k.toNat n).size) + n) → Bool,
        B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true := by
      simpa only [Fintype.card_pos_iff, nonempty_subtype] using hpos
    obtain ⟨hl, hB, hP⟩ := hc hbase
    simp only [Function.comp_apply]
    change (counter (build (ofGraph G k))).length = _ ∧ _
    rw [hbuild]
    refine ⟨hl, ?_⟩
    apply model_sound G k
      (fun j => (counter (TwoBoundary.BinaryFrontend.ofFinite B P)).getD j false)
    · rw [hbuild]
      simpa only [TwoBoundary.BinaryFrontend.ofFinite, TwoBoundary.BinaryFrontend.side,
        CNF.eval_relabel, Function.comp_def] using hB
    · rw [hbuild]
      change ∀ p ∈ P.map (CNF.relabel Fin.val), _
      intro p hmem
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      have hh := hP q hq
      change (q.any fun t => t.all fun l =>
        (counter (TwoBoundary.BinaryFrontend.ofFinite B P)).getD l.1.val false == l.2) = true at hh
      simpa only [DNF.eval, CNF.relabel, Clause.relabel, Term.eval, List.any_map,
        List.all_map, Function.comp_def, Literal.eval, Prod.map, id_eq] using hh
  · change cc.time (ofGraph G k) + cp.time (build (ofGraph G k)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G k) +
          D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G k) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G k) + D *
            ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f ≤
              W (ofGraph G k) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)


/-- Binary optimum cardinality and an actual original-vertex selection word. -/
abbrev Output := ℕ × List Bool
/-- Maximum cardinality among inclusion-minimal dominating sets. -/
@[expose] def value (out : Output) : ℕ := out.1
/-- Original-vertex selection bits, in declared order. -/
@[expose] def vertices (out : Output) : List Bool := out.2
/-- Full framed binary output, including every selected/unselected original vertex. -/
@[expose] def encOutput : Output ↪ List Bool := encPair encNat encBits

private abbrev encNatural := encPair IndependentDomination.encInput encNat

/-- Prepare the computed optimum as a signed binary recovery threshold. -/
@[expose] def prepare (x : IndependentDomination.Input × ℕ) : UpperDomination.Input :=
  (x.1, (x.2 : ℤ))
/-- Discard recovered gate/mark bits, returning only the original-vertex word and optimum value. -/
@[expose] def finish (x : UpperDomination.Input × List Bool) : Output :=
  ((threshold x.1).toNat, x.2.take (IndependentDomination.order (graph x.1)))
/-- Compute the actual optimum, recover a full extension at that threshold, then output vertices. -/
@[expose] def solve (optimum : IndependentDomination.Input → ℕ)
    (recover : UpperDomination.Input → List Bool) (g : IndependentDomination.Input) : Output :=
  let x := prepare (g, optimum g)
  finish (x, recover x)

private theorem prepare_polytime : ComputableInPolyTime prepare encNatural
    UpperDomination.encInput := by
  have hk := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.snd IndependentDomination.encInput encNat)
  unfold prepare encNatural UpperDomination.encInput
  fun_prop

private theorem finish_polytime : ComputableInPolyTime finish
    (encPair UpperDomination.encInput encBits) encOutput := by
  have hn : ComputableInPolyTime
      (fun x : UpperDomination.Input × List Bool => IndependentDomination.order (graph x.1))
      (encPair UpperDomination.encInput encBits) encUnary := by
    unfold graph UpperDomination.encInput IndependentDomination.order IndependentDomination.encInput
    fun_prop
  have ht := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.snd UpperDomination.encInput encBits) hn
  have hk := ComputableInPolyTime.intBin_toNat.comp
    (show ComputableInPolyTime (fun x : UpperDomination.Input × List Bool => threshold x.1)
      (encPair UpperDomination.encInput encBits) encIntBin from by
        unfold threshold UpperDomination.encInput; fun_prop)
  exact hk.prod ht

open Classical in
/-- Complete actual original-graph optimizer returning its attaining vertex set. The returned set
itself is inclusion-minimal dominating, has the output cardinality, and is globally optimal.
All unit-fixing, original input/counter/output writes and peak live storage are charged. -/
theorem exists_optimalWitness_sharp_certificate :
    ∃ optimize : IndependentDomination.Input → Output,
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (let out := optimize (IndependentDomination.ofGraph G)
           (vertices out).length = n ∧ Minimal G.IsDominatingSet (selected (vertices out)) ∧
             Nat.card (selected (n := n) (vertices out)) = value out ∧
               ∀ S : Set (Fin n), Minimal G.IsDominatingSet S → Nat.card S ≤ value out) ∧
          cs.time (IndependentDomination.ofGraph G) ≤
            C * ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^
              e * 2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨optimum, co, C0, e0, A0, hso, ho⟩ := Optimum.exists_optimum_sharp_certificate
  obtain ⟨recover, cw, C1, e1, A1, hsw, hw⟩ := exists_recovery_sharp_certificate
  let ci : NativeCertificate (fun g : IndependentDomination.Input => g)
      IndependentDomination.encInput IndependentDomination.encInput :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cn := ci.prod co
  have hcnS : PolyBounded (fun g => (IndependentDomination.encInput g).length) cn.space :=
    PolyBounded.self.add (PolyBounded.of_forall_le C0 e0 hso)
  obtain ⟨kn, _, hlenN⟩ := cn.computes
  have hlengthN : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encNatural (g, optimum g)).length) :=
    ((PolyBounded.const kn).mul (hcnS.add (.const 1))).mono hlenN
  let cq := NativeCertificate.ofPolyTime prepare_polytime
  have hq := NativeCertificate.ofPolyTime_isPolynomial prepare_polytime
  let cc := cq.comp cn
  have hccS := SparseCNFLeafCounter.polyBounded_comp_space cq cn hq.2 hcnS
  obtain ⟨kc, _, hlenC⟩ := cc.computes
  have hlength : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (UpperDomination.encInput (prepare (g, optimum g))).length) :=
    ((PolyBounded.const kc).mul (hccS.add (.const 1))).mono hlenC
  let cid : NativeCertificate (fun x : UpperDomination.Input => x)
      UpperDomination.encInput UpperDomination.encInput :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cr := cid.prod cw
  have hcrS : PolyBounded (fun x => (UpperDomination.encInput x).length) cr.space :=
    PolyBounded.self.add (PolyBounded.of_forall_le C1 e1 hsw)
  let pre := cr.comp cc
  have hpreS := SparseCNFLeafCounter.polyBounded_comp_space cr cc hcrS hccS
  obtain ⟨kp, _, hlenP⟩ := pre.computes
  have hlengthP : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => ((encPair UpperDomination.encInput encBits)
        (prepare (g, optimum g), recover (prepare (g, optimum g)))).length) :=
    ((PolyBounded.const kp).mul (hpreS.add (.const 1))).mono hlenP
  let post := NativeCertificate.ofPolyTime finish_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  let cs : NativeCertificate (solve optimum recover) IndependentDomination.encInput encOutput :=
    (post.comp pre).congr fun _ => rfl
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space post pre hp.2 hpreS
  let W (g : IndependentDomination.Input) := (IndependentDomination.encInput g).length +
    C0 * ((IndependentDomination.encInput g).length + 1) ^ e0 +
    cq.time (g, optimum g) + (UpperDomination.encInput (prepare (g, optimum g))).length +
    C1 * ((UpperDomination.encInput (prepare (g, optimum g))).length + 1) ^ e1 +
    post.time (prepare (g, optimum g), recover (prepare (g, optimum g))) + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((((PolyBounded.self.add ((PolyBounded.const C0).mul
      ((PolyBounded.self.add (.const 1)).pow e0))).add (hq.1.comp hlengthN)).add hlength).add
      ((PolyBounded.const C1).mul ((hlength.add (.const 1)).pow e1))).add
        (hp.1.comp hlengthP)).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨solve optimum recover, cs, C, e, A0 + A1,
    fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  obtain ⟨hopt, hupper⟩ := (ho G).1
  have hfeas : ∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧
      (optimum (IndependentDomination.ofGraph G) : ℤ) ≤ (Nat.card S : ℤ) := by
    obtain ⟨S, hm, he⟩ := hopt
    exact ⟨S, hm, by omega⟩
  obtain ⟨hl, hm, hk⟩ := (hw G (optimum (IndependentDomination.ofGraph G) : ℤ)).1 hfeas
  constructor
  · let bits := recover (ofGraph G (optimum (IndependentDomination.ofGraph G) : ℤ))
    have hs : selected (n := n) (bits.take n) = selected bits := by
      ext u
      simp only [selected, Set.mem_ofPred_eq, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt u.isLt]
    change (bits.take n).length = n ∧ Minimal G.IsDominatingSet (selected (bits.take n)) ∧
      Nat.card (selected (n := n) (bits.take n)) = optimum (IndependentDomination.ofGraph G) ∧ _
    rw [hs]
    refine ⟨?_, hm, Nat.le_antisymm (hupper _ hm) (Int.ofNat_le.mp hk), hupper⟩
    simp only [List.length_take]
    change bits.length = _ at hl
    omega
  · let g := IndependentDomination.ofGraph G
    let E := 2 ^ ((A0 + A1) * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have hE0 : 2 ^ (A0 * Nat.logLogSqrtLogScale n) ≤ E :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right A0 A1))
    have hE1 : 2 ^ (A1 * Nat.logLogSqrtLogScale n) ≤ E :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_left A1 A0))
    have ht0 := (ho G).2.trans (Nat.mul_le_mul_left _ hE0)
    have ht1 := (hw G (optimum g : ℤ)).2.trans (Nat.mul_le_mul_left _ hE1)
    change co.time g ≤ C0 * ((IndependentDomination.encInput g).length + 1) ^ e0 * E at ht0
    change cw.time (prepare (g, optimum g)) ≤
      C1 * ((UpperDomination.encInput (prepare (g, optimum g))).length + 1) ^ e1 * E at ht1
    have hlin := Nat.le_mul_of_pos_right
      ((IndependentDomination.encInput g).length + cq.time (g, optimum g) +
        (UpperDomination.encInput (prepare (g, optimum g))).length +
        post.time (prepare (g, optimum g), recover (prepare (g, optimum g)))) hE
    have htime : cs.time g ≤ W g * E := by
      change (IndependentDomination.encInput g).length + co.time g + cq.time (g, optimum g) +
        ((UpperDomination.encInput (prepare (g, optimum g))).length +
          cw.time (prepare (g, optimum g))) +
        post.time (prepare (g, optimum g), recover (prepare (g, optimum g))) ≤ _
      dsimp only [W]
      nlinarith
    exact htime.trans (Nat.mul_le_mul_right E (hCe g))

open Classical in
/-- Actual original-vertex optimum and witness output with the real single-loglog source bound. -/
theorem exists_optimalWitness_realEta_certificate :
    ∃ optimize : IndependentDomination.Input → Output,
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (let out := optimize (IndependentDomination.ofGraph G)
           (vertices out).length = n ∧ Minimal G.IsDominatingSet (selected (vertices out)) ∧
             Nat.card (selected (n := n) (vertices out)) = value out ∧
               ∀ S : Set (Fin n), Minimal G.IsDominatingSet S → Nat.card S ≤ value out) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
              e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨optimize, cs, C, e, A, hs, h⟩ := exists_optimalWitness_sharp_certificate
  refine ⟨optimize, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.UpperDomination.Witness
