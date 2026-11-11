/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Multi
public import CslibFrontier.Computability.Circuit.Boolean.Encoding.Certificate
public import CslibFrontier.Computability.Complexity.Classes.NP
import CslibFrontier.Computability.MCSP.NP
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Circuit.Encoding.MapOp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Tactic.EncLen

/-!
# Multi-output MCSP is in NP

Multi-output MCSP [IlangoLoffOliveira2020, Definition 1, p. 22:3] is in `NP` for the encoding
`Cslib.MultiMCSP.encInstance`, which writes `n`, `m` and `s` in unary and then the `m · 2^n` table
bits. A certificate is a De Morgan circuit with at most `s` gates in the format of
`Cslib.Circuits.Boolean.readCertificate`, followed by `m` fields of `n + s` bits, the output wire of
each component in unary (`Cslib.MultiMCSP.multiCertificate`). The verifier checks that the gates
form a circuit, that every output wire exists, and that output `i` agrees with component `i` on all
`2 ^ n` inputs. Since `s` is unary, certificates need no cap and are polynomially long.

`Cslib.MultiMCSP.mem_NP` is the statement over the constant-free basis of
`Cslib.Boolean.DeMorgan`, Definition 1 exactly; its verifier also rejects constant gates.
`Cslib.MultiMCSP.mem_NP_boolean` is the library variant over `Boolean.interpretation`.

## Main definitions

* `Cslib.MultiMCSP.testArity`: the number of inputs the verifier enumerates.
* `Cslib.MultiMCSP.readOutputs`, `Cslib.MultiMCSP.accepts`: the output wires read from a
  certificate, and the check of a gate list and output wires against the table bits.
* `Cslib.MultiMCSP.booleanVerifier`, `Cslib.MultiMCSP.verifier`: the verifiers over the basis with
  constants and over the constant-free basis.
* `Cslib.MultiMCSP.multiCertificate`: the certificate of a circuit.

## Main results

* `Cslib.MultiMCSP.exists_circuit_of_booleanVerifier`,
  `Cslib.MultiMCSP.booleanVerifier_multiCertificate_append`: soundness and completeness of the
  verifier over the basis with constants.
* `Cslib.MultiMCSP.exists_circuit_of_verifier`, `Cslib.MultiMCSP.verifier_multiCertificate_append`:
  soundness and completeness over the constant-free basis.
* `Cslib.MultiMCSP.mem_NP`: Multi-output MCSP over the constant-free basis is in `NP`.
* `Cslib.MultiMCSP.mem_NP_boolean`: the library variant over `Boolean.interpretation` is in `NP`.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.MultiMCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-! ### The verifier -/

/-- The number of inputs on which the verifier compares outputs with the table: `n` when there is a
component, `0` when there is none. With no component there is nothing to compare, and the guard
keeps the enumeration of `2 ^ n` inputs polynomial in the encoding, which then has no table bits. -/
def testArity (n m : ℕ) : ℕ := n * min m 1

theorem testArity_of_pos {n m : ℕ} (hm : 0 < m) : testArity n m = n := by
  simp [testArity, Nat.min_eq_right (Nat.one_le_iff_ne_zero.2 hm.ne')]

@[simp] theorem testArity_zero (n : ℕ) : testArity n 0 = 0 := by
  simp [testArity]

/-- The `m` output wires read from the bits that follow a single-output certificate for `n` inputs
and at most `s` gates: `m` fields of `n + s` bits, each read as its number of ones. -/
def readOutputs (n m s : ℕ) (w : List Bool) : List ℕ :=
  (BitString.listRows m (n + s) (w.drop (certLength n s))).map (List.count true)

/-- Whether the gates `gates` and output wires `outs` describe a circuit on `n` inputs whose output
`i` agrees with row `i` of `bits` on all inputs; the rows have `2 ^ n` bits, in the order of
`MCSP.truthTable`. -/
def accepts (n m : ℕ) (bits : List Bool) (gates : List (Op × List ℕ)) (outs : List ℕ) : Bool :=
  codeCheck signature n gates && outs.all (· < n + gates.length) &&
    (BitString.enumList (testArity n m)).all fun y =>
      ((BitString.listRows m (2 ^ testArity n m) bits).zip outs).all fun r =>
        evalOutput y gates r.2 == MCSP.tableValue r.1 y

/-- The verifier over cslib's basis with constants: the certificate must describe at most
`threshold` gates and one output wire per component (`readOutputs`) that agree with the table. -/
def booleanVerifier (p : Instance × List Bool) : Bool :=
  accepts p.1.arity p.1.outputs p.1.tableBits
    (readCertificate p.1.arity p.1.threshold p.2).1
    (readOutputs p.1.arity p.1.outputs p.1.threshold p.2)

/-- Whether an operation of cslib's basis is not a constant. -/
def nonConst : Op → Bool
  | .const _ => false
  | _ => true

/-- The verifier over the constant-free basis [IlangoLoffOliveira2020, Definition 1]:
`booleanVerifier`, and no gate is a constant. -/
def verifier (p : Instance × List Bool) : Bool :=
  booleanVerifier p && (readCertificate p.1.arity p.1.threshold p.2).1.all fun g => nonConst g.1

/-! ### Rows of the table -/

/-- Row `i` of the table bits is the truth table of component `i`. -/
theorem listRows_tableBits (x : Instance) :
    BitString.listRows x.outputs (2 ^ x.arity) x.tableBits =
      List.ofFn fun i => List.ofFn (x.table i) := by
  rw [Instance.tableBits_eq_flatten]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [BitString.listRows, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [List.ofFn_eq_map, ← List.flatMap_def]
  have := BitString.listRow_flatMap_append (width := 2 ^ x.arity)
    (fun i => List.ofFn (x.table i)) (List.finRange x.outputs) (by simp) [] i (by simpa using h₂)
  simpa using this

/-! ### Soundness -/

/-- **Soundness over the basis with constants.** An accepted certificate describes a circuit with
at most `threshold` gates that computes the function of the instance, and its gate list is the one
read from the certificate. -/
theorem exists_circuit_of_booleanVerifier {x : Instance} {w : List Bool}
    (hw : booleanVerifier (x, w) = true) :
    ∃ c : Circuit signature x.arity x.outputs, c.Computes interpretation x.function ∧
      c.size ≤ x.threshold ∧ c.code.1 = (readCertificate x.arity x.threshold w).1 := by
  set gates := (readCertificate x.arity x.threshold w).1
  set outs := readOutputs x.arity x.outputs x.threshold w
  have hlen : outs.length = x.outputs := by simp [outs, readOutputs]
  simp only [booleanVerifier, accepts, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    codeCheck_eq_true_iff, beq_iff_eq] at hw
  obtain ⟨⟨hcode, hout⟩, hall⟩ := hw
  change Program.IsCodeFrom signature x.arity 0 gates at hcode
  have hsome : (Circuit.ofCode x.arity x.outputs (gates, outs) :
      Option (Circuit signature _ _)).isSome :=
    Circuit.isSome_ofCode_iff.2 ⟨hcode, hlen, hout⟩
  set c : Circuit signature x.arity x.outputs :=
    (Circuit.ofCode x.arity x.outputs (gates, outs)).get hsome
  have hc : c.code = (gates, outs) := Circuit.code_of_ofCode_eq_some (Option.some_get _).symm
  refine ⟨c, fun y => funext fun i => ?_, ?_, by rw [hc]⟩
  · have hi : (i : ℕ) < outs.length := by rw [hlen]; exact i.isLt
    have houtput : (c.outputs i).toNat = outs[i] := by
      have h₁ : c.code.2[(i : ℕ)]? = some (c.outputs i).toNat := by simp [Circuit.code]
      simp only [hc] at h₁
      rw [List.getElem?_eq_getElem hi] at h₁
      exact (Option.some.inj h₁).symm
    have hk : testArity x.arity x.outputs = x.arity := testArity_of_pos (Fin.pos i)
    have hmem : (List.ofFn (x.table i), outs[i]) ∈
        (BitString.listRows x.outputs (2 ^ testArity x.arity x.outputs) x.tableBits).zip outs := by
      rw [hk, listRows_tableBits]
      exact List.mem_iff_getElem.2 ⟨i, by simp [hlen], by simp⟩
    have := hall (List.ofFn y) (by rw [hk]; exact BitString.mem_enumList.2 List.length_ofFn) _ hmem
    rw [Circuit.eval_eq_evalOutput, houtput, show c.code.1 = gates by rw [hc], this]
    exact MCSP.getD_boundedBinaryValue_reverse_ofFn (x.table i) y false
  · calc c.size = gates.length := by rw [← Circuit.length_code_fst, hc]
      _ ≤ x.threshold := length_readCertificate_le _ _ _

/-! ### Completeness -/

/-- The certificate of a circuit with at most `s` gates and `m` outputs: its single-output
certificate (`Circuits.Boolean.certificate`, with output field `0`), then the output wire of each
component in a field of `n + s` bits. -/
def multiCertificate {n m : ℕ} (s : ℕ) (c : Circuit signature n m) : List Bool :=
  certificate n s c.code.1 0 ++ c.code.2.flatMap (unaryField (n + s))

private theorem le_of_mem_code_snd {n m s : ℕ} {c : Circuit signature n m} (hs : c.size ≤ s)
    {o : ℕ} (ho : o ∈ c.code.2) : o < n + c.size ∧ o ≤ n + s := by
  obtain ⟨j, rfl⟩ : ∃ j, (c.outputs j).toNat = o := by simpa [Circuit.code] using ho
  have := (c.outputs j).toNat_lt
  omega

private theorem length_certificate_code_fst {n m s : ℕ} (c : Circuit signature n m)
    (hs : c.size ≤ s) : (certificate n s c.code.1 0).length = certLength n s := by
  have hcode := c.isCodeFrom_code
  refine length_certificate (by rw [Circuit.length_code_fst]; exact hs) (by omega) ?_
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have := (hcode.getElem j hj).2 i hi
  have : j < c.size := by rwa [Circuit.length_code_fst] at hj
  omega

/-- The certificate of a circuit with at most `s` gates has length `certLength n s + m (n + s)`. -/
theorem length_multiCertificate {n m s : ℕ} (c : Circuit signature n m) (hs : c.size ≤ s) :
    (multiCertificate s c).length = certLength n s + m * (n + s) := by
  rw [multiCertificate, List.length_append, length_certificate_code_fst c hs, List.length_flatMap,
    List.map_congr_left fun o ho => length_unaryField _ _ (le_of_mem_code_snd hs ho).2,
    List.map_const', List.sum_replicate, smul_eq_mul]
  simp [Circuit.code]

private theorem readCertificate_multiCertificate_append {n m s : ℕ} (c : Circuit signature n m)
    (hs : c.size ≤ s) (extra : List Bool) :
    (readCertificate n s (multiCertificate s c ++ extra)).1 = c.code.1 := by
  rw [multiCertificate, List.append_assoc, readCertificate_certificate_append c.isCodeFrom_code
    (by rw [Circuit.length_code_fst]; exact hs) (by omega)]

private theorem readOutputs_multiCertificate_append {n m s : ℕ} (c : Circuit signature n m)
    (hs : c.size ≤ s) (extra : List Bool) :
    readOutputs n m s (multiCertificate s c ++ extra) = c.code.2 := by
  have hfields : ∀ o ∈ c.code.2, (unaryField (n + s) o).length = n + s := fun o ho =>
    length_unaryField _ _ (le_of_mem_code_snd hs ho).2
  have hm : c.code.2.length = m := by simp [Circuit.code]
  rw [readOutputs, multiCertificate, List.append_assoc,
    List.drop_left' (length_certificate_code_fst c hs)]
  refine List.ext_getElem (by simp [hm]) fun j h₁ h₂ => ?_
  simp only [BitString.listRows, List.getElem_map, List.getElem_range]
  rw [BitString.listRow_flatMap_append _ _ hfields _ j h₂, count_unaryField]

/-- **Completeness over the basis with constants.** A circuit with at most `threshold` gates that
computes the function of the instance has a certificate of length
`certLength n s + m (n + s)`, accepted whatever bits follow it. -/
theorem booleanVerifier_multiCertificate_append {x : Instance}
    {c : Circuit signature x.arity x.outputs} (hc : c.Computes interpretation x.function)
    (hs : c.size ≤ x.threshold) (extra : List Bool) :
    booleanVerifier (x, multiCertificate x.threshold c ++ extra) = true := by
  simp only [booleanVerifier, readCertificate_multiCertificate_append c hs,
    readOutputs_multiCertificate_append c hs, accepts, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, codeCheck_eq_true_iff, beq_iff_eq]
  refine ⟨⟨c.isCodeFrom_code, fun o ho => by
    rw [Circuit.length_code_fst]; exact (le_of_mem_code_snd hs ho).1⟩, fun y hy r hr => ?_⟩
  rcases Nat.eq_zero_or_pos x.outputs with hm | hm
  · have hnil : BitString.listRows x.outputs (2 ^ testArity x.arity x.outputs) x.tableBits = [] :=
      List.eq_nil_of_length_eq_zero (by simp [hm])
    simp [hnil] at hr
  rw [testArity_of_pos hm, listRows_tableBits] at hr
  rw [testArity_of_pos hm] at hy
  obtain ⟨y', rfl⟩ : ∃ y' : BitString x.arity, List.ofFn y' = y :=
    ⟨BitString.ofList x.arity y, BitString.ofFn_ofList (BitString.mem_enumList.1 hy)⟩
  obtain ⟨j, hj, hrj⟩ := List.mem_iff_getElem.1 hr
  have hj' : j < x.outputs := by simp only [List.length_zip, List.length_ofFn] at hj; omega
  obtain rfl : r = (List.ofFn (x.table ⟨j, hj'⟩), (c.outputs ⟨j, hj'⟩).toNat) := by
    rw [← hrj]
    simp [Circuit.code]
  rw [← Circuit.eval_eq_evalOutput, hc y']
  exact (MCSP.getD_boundedBinaryValue_reverse_ofFn (x.table ⟨j, hj'⟩) y' false).symm

/-! ### The constant-free basis -/

/-- The operation of the constant-free basis that a non-constant operation of cslib's basis is;
constants, which accepted certificates do not contain, go to `.not`. -/
private def ofBooleanOp : Op → Boolean.DeMorgan.Op
  | .const _ => .not
  | .not => .not
  | .and => .and
  | .or => .or

private theorem toBoolean_ofBooleanOp {op : Op} (h : nonConst op = true) :
    Boolean.DeMorgan.toBoolean (ofBooleanOp op) = op := by
  cases op <;> first | rfl | simp [nonConst] at h

private theorem arity_ofBooleanOp {op : Op} (h : nonConst op = true) :
    Boolean.DeMorgan.signature.Arity (ofBooleanOp op) = signature.Arity op := by
  cases op <;> first | rfl | simp [nonConst] at h

/-- A circuit over cslib's basis without constant gates is the image of a circuit over the
constant-free basis. -/
private theorem exists_mapOp_eq {n m : ℕ} (c : Circuit signature n m)
    (h : ∀ g ∈ c.code.1, nonConst g.1 = true) :
    ∃ d : Circuit Boolean.DeMorgan.signature n m, d.mapOp Boolean.DeMorgan.toBoolean = c := by
  set gates := c.code.1.map fun g => (ofBooleanOp g.1, g.2)
  have hmap : gates.map (fun g => (Boolean.DeMorgan.toBoolean g.1, g.2)) = c.code.1 := by
    conv_rhs => rw [← List.map_id' c.code.1]
    rw [List.map_map]
    exact List.map_congr_left fun g hg => Prod.ext (toBoolean_ofBooleanOp (h g hg)) rfl
  have hcode : Program.IsCodeFrom Boolean.DeMorgan.signature n 0 gates := by
    refine Program.isCodeFrom_of_getElem fun j hj => ?_
    have hj' : j < c.code.1.length := by simpa [gates] using hj
    obtain ⟨h₁, h₂⟩ := c.isCodeFrom_code.getElem j hj'
    refine ⟨?_, by simpa [gates] using h₂⟩
    have hg : gates[j] = (ofBooleanOp c.code.1[j].1, c.code.1[j].2) := by
      simp only [gates, List.getElem_map]
    rw [hg, arity_ofBooleanOp (h _ (List.getElem_mem hj'))]
    exact h₁
  have hsome : (Circuit.ofCode n m (gates, c.code.2) :
      Option (Circuit Boolean.DeMorgan.signature n m)).isSome := by
    obtain ⟨-, h₂, h₃⟩ := Circuit.isSome_ofCode_iff.1 (by rw [Circuit.ofCode_code]; rfl :
      (Circuit.ofCode n m c.code : Option (Circuit signature n m)).isSome)
    exact Circuit.isSome_ofCode_iff.2 ⟨hcode, h₂, by simpa [gates] using h₃⟩
  set d : Circuit Boolean.DeMorgan.signature n m :=
    (Circuit.ofCode n m (gates, c.code.2)).get hsome
  have hd : d.code = (gates, c.code.2) := Circuit.code_of_ofCode_eq_some (Option.some_get _).symm
  refine ⟨d, Circuit.code_injective ?_⟩
  rw [Circuit.code_mapOp, hd, hmap]

/-- **Soundness over the constant-free basis.** An accepted certificate describes a constant-free
circuit with at most `threshold` gates that computes the function of the instance. -/
theorem exists_circuit_of_verifier {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    ∃ d : Circuit Boolean.DeMorgan.signature x.arity x.outputs,
      d.Computes Boolean.DeMorgan.interpretation x.function ∧ d.size ≤ x.threshold := by
  simp only [verifier, Bool.and_eq_true, List.all_eq_true] at hw
  obtain ⟨c, hc, hs, hcode⟩ := exists_circuit_of_booleanVerifier hw.1
  obtain ⟨d, rfl⟩ := exists_mapOp_eq c fun g hg => hw.2 g (hcode ▸ hg)
  refine ⟨d, fun y => ?_, by simpa using hs⟩
  rw [← hc y, Circuit.eval_mapOp (I := Boolean.DeMorgan.interpretation)]

/-- **Completeness over the constant-free basis.** A constant-free circuit with at most `threshold`
gates that computes the function of the instance has a certificate, accepted whatever bits follow
it: that of its image in cslib's basis. -/
theorem verifier_multiCertificate_append {x : Instance}
    {d : Circuit Boolean.DeMorgan.signature x.arity x.outputs}
    (hd : d.Computes Boolean.DeMorgan.interpretation x.function) (hs : d.size ≤ x.threshold)
    (extra : List Bool) :
    verifier (x, multiCertificate x.threshold (d.mapOp Boolean.DeMorgan.toBoolean) ++ extra) =
      true := by
  have hcs : (d.mapOp Boolean.DeMorgan.toBoolean).size ≤ x.threshold := by simpa using hs
  simp only [verifier, booleanVerifier_multiCertificate_append hd.mapOp hcs, Bool.true_and,
    readCertificate_multiCertificate_append _ hcs, List.all_eq_true]
  intro g hg
  rw [Circuit.code_mapOp] at hg
  obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
  cases g'.1 <;> rfl

/-! ### Certificates are polynomially long -/

/-- The polynomial bounding the length of certificates. -/
noncomputable def certPolynomial : Polynomial ℕ := 6 * (Polynomial.X + 1) ^ 2

private theorem certLength_le (x : Instance) :
    certLength x.arity x.threshold + x.outputs * (x.arity + x.threshold) ≤
      certPolynomial.eval (encInstance x).length := by
  have hn : x.arity ≤ (encInstance x).length := by enc_len [encInstance_apply]
  have hm : x.outputs ≤ (encInstance x).length := by enc_len [encInstance_apply]
  have hs : x.threshold ≤ (encInstance x).length := by enc_len [encInstance_apply]
  set L := (encInstance x).length
  simp only [certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

/-! ### Polynomial time -/

open ComputableInPolyTime

attribute [local irreducible] ComputableInPolyTime

/-- `accepts`, with its arguments computed in polynomial time, is polynomial-time when the
enumeration of `2 ^ testArity n m` inputs is polynomially bounded in the input length. -/
private theorem computableInPolyTime_accepts {γ : Type} {encIn : γ ↪ List Bool}
    {n m : γ → ℕ} {bits : γ → List Bool} {gates : γ → List (Op × List ℕ)} {outs : γ → List ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hm : ComputableInPolyTime m encIn encUnary)
    (hbits : ComputableInPolyTime bits encIn encBits)
    (hgates : ComputableInPolyTime gates encIn (encList encGate))
    (houts : ComputableInPolyTime outs encIn (encList encNat))
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ testArity (n a) (m a) * (2 * testArity (n a) (m a) + 1) ≤
      size (encIn a).length) :
    ComputableInPolyTime (fun a => accepts (n a) (m a) (bits a) (gates a) (outs a))
      encIn encBool := by
  have hk : ComputableInPolyTime (fun a => testArity (n a) (m a)) encIn encUnary := by
    unfold testArity
    exact unary_mul' hn ((ComputableInPolyTime.of_tidy
      ComputableTidilyInPolyTime.unary_min).comp (hm.prod (const 1)))
  have henum := bitsEnumList hk hsize hbudget
  have hwidth : ComputableInPolyTime (fun a => 2 ^ testArity (n a) (m a)) encIn encUnary := by
    simpa only [Function.comp_def, BitString.length_enumList] using (length_list encBits).comp henum
  have hrows := bitsRowsWithInput hm hwidth hbits
  have hpairs := (zip encBits encNat).comp (hrows.prod houts)
  have hcode := computableInPolyTime_codeCheck hn hgates
  have hbound : ComputableInPolyTime (fun a => (outs a).all (· < n a + (gates a).length))
      encIn encBool :=
    allWithInput houts (binary_lt' (snd encIn encNat) (unary_to_binary.comp (unary_add.comp
      ((hn.comp (fst encIn encNat)).prod ((length_list encGate).comp
        (hgates.comp (fst encIn encNat)))))))
  have hinner : ComputableInPolyTime
      (fun q : (γ × List Bool) × (List Bool × ℕ) =>
        evalOutput q.1.2 (gates q.1.1) q.2.2 == MCSP.tableValue q.2.1 q.1.2)
      (encPair (encPair encIn encBits) (encPair encBits encNat)) encBool :=
    (computableInPolyTime_evalOutput (fst _ _).snd' (hgates.comp (fst _ _).fst')
      (snd _ _).snd').beq (MCSP.computableInPolyTime_tableValue.comp
        ((snd _ _).fst'.prod (fst _ _).snd'))
  have houter : ComputableInPolyTime
      (fun p : γ × List Bool => ((BitString.listRows (m p.1) (2 ^ testArity (n p.1) (m p.1))
        (bits p.1)).zip (outs p.1)).all fun r => evalOutput p.2 (gates p.1) r.2 ==
          MCSP.tableValue r.1 p.2)
      (encPair encIn encBits) encBool :=
    allWithInput (hpairs.comp (fst encIn encBits)) hinner
  unfold accepts
  exact bool_and' (bool_and' hcode hbound) (allWithInput henum houter)

/-- The fields of an instance, as `encInstance` writes them. -/
private theorem computableInPolyTime_fields :
    ComputableInPolyTime (fun x : Instance => (x.arity, x.outputs, x.threshold, x.tableBits))
      encInstance encUnaryFields :=
  .of_eq fun _ => rfl

/-- The verifier over the basis with constants is polynomial-time. -/
theorem computableInPolyTime_booleanVerifier :
    ComputableInPolyTime booleanVerifier (encPair encInstance encBits) encBool := by
  have hf := computableInPolyTime_fields.comp (fst encInstance encBits)
  have hn : ComputableInPolyTime (fun p : Instance × List Bool => p.1.arity)
      (encPair encInstance encBits) encUnary := hf.fst'
  have hm : ComputableInPolyTime (fun p : Instance × List Bool => p.1.outputs)
      (encPair encInstance encBits) encUnary := hf.snd'.fst'
  have hs : ComputableInPolyTime (fun p : Instance × List Bool => p.1.threshold)
      (encPair encInstance encBits) encUnary := hf.snd'.snd'.fst'
  have hbits : ComputableInPolyTime (fun p : Instance × List Bool => p.1.tableBits)
      (encPair encInstance encBits) encBits := hf.snd'.snd'.snd'
  have hw := snd encInstance encBits
  have hread := computableInPolyTime_readCertificate hn hs hw
  have hdrop : ComputableInPolyTime
      (fun p : Instance × List Bool => p.2.drop (certLength p.1.arity p.1.threshold))
      (encPair encInstance encBits) encBits :=
    bitsDropWithInput hw (by unfold certLength; fun_prop)
  have houts : ComputableInPolyTime
      (fun p : Instance × List Bool => readOutputs p.1.arity p.1.outputs p.1.threshold p.2)
      (encPair encInstance encBits) (encList encNat) := by
    unfold readOutputs
    exact mapWithInput (bitsRowsWithInput hm (unary_add' hn hs) hdrop)
      (unary_to_binary.comp (bitsCountWithInput (snd _ _) (const true)))
  refine computableInPolyTime_accepts hn hm hbits hread.fst' houts
    (size := fun L => L * L) (by fun_prop) fun p => ?_
  rcases Nat.eq_zero_or_pos p.1.outputs with h | h
  · have : 3 ≤ (encPair encInstance encBits p).length := by
      enc_len [encInstance_apply]
    simp only [testArity, h, Nat.zero_min, Nat.mul_zero, pow_zero, Nat.one_mul]
    nlinarith
  · rw [testArity_of_pos h]
    have hT : 2 ^ p.1.arity ≤ (encPair encInstance encBits p).length := by
      have : p.1.outputs * 2 ^ p.1.arity ≤ (encPair encInstance encBits p).length := by
        enc_len [encInstance_apply, Instance.length_tableBits]
      exact (Nat.le_mul_of_pos_left _ h).trans this
    have hn' : 2 * p.1.arity + 1 ≤ (encPair encInstance encBits p).length := by
      enc_len [encInstance_apply]
    exact Nat.mul_le_mul hT hn'

/-- The verifier over the constant-free basis is polynomial-time. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encInstance encBits) encBool := by
  have hf := computableInPolyTime_fields.comp (fst encInstance encBits)
  have hread := computableInPolyTime_readCertificate (hf.fst') (hf.snd'.snd'.fst')
    (snd encInstance encBits)
  have hnc : ComputableInPolyTime (fun q : (Instance × List Bool) × (Op × List ℕ) => nonConst q.2.1)
      (encPair (encPair encInstance encBits) encGate) encBool :=
    (of_finite (encIn := encOp) (encOut := encBool) nonConst).comp (snd _ _).fst'
  unfold verifier
  exact bool_and' computableInPolyTime_booleanVerifier (allWithInput hread.fst' hnc)

/-! ### Membership in NP -/

/-- `booleanVerifier` verifies the library variant over `Boolean.interpretation`, with
certificates of length `certPolynomial`. -/
theorem isVerifier_boolean :
    IsVerifier encInstance certPolynomial booleanVerifier (MultiMCSP interpretation) := by
  refine IsVerifier.of_padding (fun x w _ hw => ?_) fun x hx => ?_
  · obtain ⟨c, hc, hs, -⟩ := exists_circuit_of_booleanVerifier hw
    exact mem_iff_exists_circuit.2 ⟨c, hc, hs⟩
  · obtain ⟨c, hc, hs⟩ := mem_iff_exists_circuit.1 hx
    exact ⟨multiCertificate x.threshold c, (length_multiCertificate c hs).symm ▸ certLength_le x,
      fun k => booleanVerifier_multiCertificate_append hc hs _⟩

/-- `verifier` verifies Multi-output MCSP over the constant-free basis, with certificates of length
`certPolynomial`. -/
theorem isVerifier :
    IsVerifier encInstance certPolynomial verifier
      (MultiMCSP Boolean.DeMorgan.interpretation) := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_iff_exists_circuit.2
    (exists_circuit_of_verifier hw)) fun x hx => ?_
  obtain ⟨d, hd, hs⟩ := mem_iff_exists_circuit.1 hx
  have hcs : (d.mapOp Boolean.DeMorgan.toBoolean).size ≤ x.threshold := by simpa using hs
  exact ⟨multiCertificate x.threshold (d.mapOp Boolean.DeMorgan.toBoolean),
    (length_multiCertificate _ hcs).symm ▸ certLength_le x,
    fun _ => verifier_multiCertificate_append hd hs _⟩

/-- **Multi-output MCSP is in `NP`** [IlangoLoffOliveira2020, Definition 1]: over the constant-free
basis of fan-in-two AND and OR and NOT, for the encoding `encInstance`. -/
theorem mem_NP : MultiMCSP Boolean.DeMorgan.interpretation ∈ NP encInstance :=
  ⟨certPolynomial, verifier, computableInPolyTime_verifier, isVerifier⟩

/-- The library variant over cslib's basis with constants is in `NP`. -/
theorem mem_NP_boolean : MultiMCSP interpretation ∈ NP encInstance :=
  ⟨certPolynomial, booleanVerifier, computableInPolyTime_booleanVerifier, isVerifier_boolean⟩

end Cslib.MultiMCSP
