/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.TQBF.Tokens
public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.ZMod.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Probabilistic.PPT.Capture
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Words of the machine verifier for quantified Boolean formulas

The machine realizing the verifier of `Cslib.Complexity.QBFProtocol.verifyAt` over `ZMod p`
represents ring elements by natural numbers below `p`, in unary, which is polynomial since `p` is
chosen of polynomial size. This file gives the arithmetic it performs and its words:

* the operations of the arithmetization modulo `p` (`Cslib.Complexity.QBFProtocol.subMod`,
  `Cslib.Complexity.QBFProtocol.connectiveMod`, `Cslib.Complexity.QBFProtocol.operatorMod`) and
  Horner's rule modulo `p` (`Cslib.Complexity.QBFProtocol.hornerMod`), which compute in `ZMod p`;
* points as lists of pairs of a variable and its value (`Cslib.Complexity.QBFProtocol.lookupPt`,
  `Cslib.Complexity.QBFProtocol.normPt`, `Cslib.Complexity.QBFProtocol.updatePt`), which agree
  with the point of the protocol on the variables of a list `xs`
  (`Cslib.Complexity.QBFProtocol.canonPt`);
* the decoding of a reply word as `D + 1` rows of `width p` bits, each read in binary modulo `p`
  (`Cslib.Complexity.QBFProtocol.decodeReply`), and the encoding of a reply by the honest prover
  (`Cslib.Complexity.QBFProtocol.encodeReply`), which it inverts;
* the samples, a uniform index in the dyadic range above `p` reduced modulo `p`
  (`Cslib.Complexity.QBFProtocol.sampleMod`), which give every residue probability at most `2 / p`
  (`Cslib.Complexity.QBFProtocol.eval_sampleMod_le`) with a fixed number of fair coins.

All are polynomial-time in their unary or binary inputs.

## Main definitions

* `Cslib.Complexity.QBFProtocol.connectiveMod`, `Cslib.Complexity.QBFProtocol.operatorMod`,
  `Cslib.Complexity.QBFProtocol.hornerMod`: arithmetic modulo `p`.
* `Cslib.Complexity.QBFProtocol.canonPt`, `Cslib.Complexity.QBFProtocol.updatePt`: points.
* `Cslib.Complexity.QBFProtocol.decodeReply`, `Cslib.Complexity.QBFProtocol.encodeReply`: replies.
* `Cslib.Complexity.QBFProtocol.sampleMod`: samples.

## Main results

* `Cslib.Complexity.QBFProtocol.natCast_operatorMod`,
  `Cslib.Complexity.QBFProtocol.natCast_hornerMod`: the arithmetic computes in `ZMod p`.
* `Cslib.Complexity.QBFProtocol.updatePt_canonPt`: updating a point.
* `Cslib.Complexity.QBFProtocol.decodeReply_encodeReply`: decoding inverts the honest encoding.
* `Cslib.Complexity.QBFProtocol.eval_sampleMod_le`: the samples are nearly uniform.

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial Turing.MultiTapeTM Cslib.Probability Cslib.ProbComp
open scoped ENNReal

/-! ### Arithmetic modulo `p` -/

/-- The difference `a - b` modulo `p`. -/
def subMod (p a b : ℕ) : ℕ := (a % p + (p - b % p)) % p

/-- The value of a connective on residues modulo `p`. -/
def connectiveMod (p : ℕ) : ArithQBF.Connective → ℕ → ℕ → ℕ
  | .and, a, b => a * b % p
  | .or, a, b => subMod p 1 (subMod p 1 a * subMod p 1 b)

/-- The value of an operator on residues modulo `p`. -/
def operatorMod (p : ℕ) : ArithQBF.Operator → ℕ → ℕ → ℕ → ℕ
  | .ex, _, a, b => subMod p 1 (subMod p 1 a * subMod p 1 b)
  | .all, _, a, b => a * b % p
  | .lin, t, a, b => (subMod p 1 t * a + t * b) % p

/-- The value at `z` of a coefficient list modulo `p`, by Horner's rule from the last
coefficient. The modulus `0` is read as `1`, so that the intermediate values stay small. -/
def hornerMod (p z : ℕ) (l : List ℕ) : ℕ :=
  l.reverse.foldl (fun acc a => (a + z * acc) % (p - 1 + 1)) 0

variable {p : ℕ}

theorem natCast_subMod [NeZero p] (a b : ℕ) : ((subMod p a b : ℕ) : ZMod p) = a - b := by
  unfold subMod
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ (NeZero.pos p)).le,
    ZMod.natCast_mod, ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem natCast_connectiveMod [NeZero p] (o : ArithQBF.Connective) (a b : ℕ) :
    ((connectiveMod p o a b : ℕ) : ZMod p) = o.apply (a : ZMod p) b := by
  cases o
  · rw [connectiveMod, ZMod.natCast_mod, Nat.cast_mul, ArithQBF.Connective.apply]
  · rw [connectiveMod, natCast_subMod, Nat.cast_mul, natCast_subMod, natCast_subMod,
      ArithQBF.Connective.apply, Nat.cast_one]

/-- For `p ≠ 0`, `operatorMod` computes the operators of the arithmetization in `ZMod p`. -/
theorem natCast_operatorMod [NeZero p] (o : ArithQBF.Operator) (t a b : ℕ) :
    ((operatorMod p o t a b : ℕ) : ZMod p) = o.apply (t : ZMod p) a b := by
  cases o
  · rw [operatorMod, natCast_subMod, Nat.cast_mul, natCast_subMod, natCast_subMod,
      ArithQBF.Operator.apply, Nat.cast_one]
  · rw [operatorMod, ZMod.natCast_mod, Nat.cast_mul, ArithQBF.Operator.apply]
  · rw [operatorMod, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, natCast_subMod,
      ArithQBF.Operator.apply, Nat.cast_one]

/-- For `p ≠ 0`, Horner's rule modulo `p` evaluates the coefficient list `l` at `z` in
`ZMod p`. -/
theorem natCast_hornerMod [NeZero p] (z : ℕ) (l : List ℕ) :
    ((hornerMod p z l : ℕ) : ZMod p) = evalCoeffList (z : ZMod p) (l.map Nat.cast) := by
  rw [hornerMod, List.foldl_reverse, Nat.sub_add_cancel NeZero.one_le]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ih, List.map_cons,
      evalCoeffList_cons]

theorem subMod_lt [NeZero p] (a b : ℕ) : subMod p a b < p := Nat.mod_lt _ (NeZero.pos p)

theorem connectiveMod_lt [NeZero p] (o : ArithQBF.Connective) (a b : ℕ) :
    connectiveMod p o a b < p := by
  cases o
  · exact Nat.mod_lt _ (NeZero.pos p)
  · exact subMod_lt _ _

theorem operatorMod_lt [NeZero p] (o : ArithQBF.Operator) (t a b : ℕ) :
    operatorMod p o t a b < p := by
  cases o
  · exact subMod_lt _ _
  · exact Nat.mod_lt _ (NeZero.pos p)
  · exact Nat.mod_lt _ (NeZero.pos p)

theorem hornerMod_lt [NeZero p] (z : ℕ) (l : List ℕ) : hornerMod p z l < p := by
  rw [hornerMod, List.foldl_reverse, Nat.sub_add_cancel NeZero.one_le]
  cases l with
  | nil => exact NeZero.pos p
  | cons a l => exact Nat.mod_lt _ (NeZero.pos p)

/-- A residue below `p` compares with an element of `ZMod p` through its value. -/
theorem mod_eq_val_mod_iff [NeZero p] (a : ℕ) (c : ZMod p) :
    a % p = c.val % p ↔ (a : ZMod p) = c := by
  rw [← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val]

/-! ### Points -/

/-- The value of the variable `w` at a point given as a list of pairs of a variable and its value:
the value of the first pair for `w`, or `0`. -/
def lookupPt (pt : List (ℕ × ℕ)) (w : ℕ) : ℕ := (pt.find? fun q => q.1 == w).elim 0 Prod.snd

/-- The point `r` on the variables of `xs`, as a list of pairs of a variable and its value. -/
def canonPt (xs : List ℕ) (r : ℕ → ZMod p) : List (ℕ × ℕ) := xs.map fun x => (x, (r x).val)

/-- A point rebuilt on the variables of `xs`, with values reduced modulo `p`. -/
def normPt (p : ℕ) (xs : List ℕ) (pt : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  xs.map fun x => (x, lookupPt pt x % p)

/-- A point rebuilt on the variables of `xs`, with the variable `v` set to `z`. -/
def updatePt (p : ℕ) (xs : List ℕ) (pt : List (ℕ × ℕ)) (v z : ℕ) : List (ℕ × ℕ) :=
  xs.map fun x => (x, if x = v then z % p else lookupPt pt x % p)

theorem lookupPt_canonPt {xs : List ℕ} (r : ℕ → ZMod p) {w : ℕ} (hw : w ∈ xs) :
    lookupPt (canonPt xs r) w = (r w).val := by
  induction xs with
  | nil => exact absurd hw List.not_mem_nil
  | cons x xs ih =>
    by_cases hx : x = w
    · subst hx
      simp [lookupPt, canonPt]
    · have hw' : w ∈ xs := (List.mem_cons.1 hw).resolve_left (Ne.symm hx)
      have hb : (x == w) = false := beq_false_of_ne hx
      have := ih hw'
      simp only [lookupPt, canonPt, List.map_cons, List.find?_cons, hb] at this ⊢
      exact this

theorem normPt_canonPt [NeZero p] (xs : List ℕ) (r : ℕ → ZMod p) :
    normPt p xs (canonPt xs r) = canonPt xs r := by
  unfold normPt
  conv_rhs => rw [canonPt]
  refine List.map_congr_left fun x hx => ?_
  rw [lookupPt_canonPt r hx, Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- For `p ≠ 0`, setting the variable `v` to `z` in the point `r` on the variables of `xs` gives
the point `Function.update r v z` on the same variables. -/
theorem updatePt_canonPt [NeZero p] (xs : List ℕ) (r : ℕ → ZMod p) (v z : ℕ) :
    updatePt p xs (canonPt xs r) v z = canonPt xs (Function.update r v (z : ZMod p)) := by
  unfold updatePt canonPt
  refine List.map_congr_left fun x hx => ?_
  by_cases hxv : x = v
  · subst hxv
    rw [ite_eq_left rfl, Function.update_self, ZMod.val_natCast]
  · rw [ite_eq_right hxv, Function.update_of_ne hxv, ← canonPt, lookupPt_canonPt r hx,
      Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-! ### Replies -/

/-- The number of bits of a residue modulo `p` in a reply. -/
def width (p : ℕ) : ℕ := Nat.log 2 p + 1

/-- The number of bits of a reply that the verifier reads: `D + 1` rows. -/
def replyLimit (p D : ℕ) : ℕ := (D + 1) * width p

/-- A reply read as `D + 1` rows of `width p` bits, missing bits being `false`, each row read in
binary and reduced modulo `p`. -/
def decodeReply (p D : ℕ) (word : List Bool) : List ℕ :=
  (BitString.listRows (D + 1) (width p) word).map fun row =>
    BitString.boundedBinaryValue (dyadicSize p) row % p

/-- The reply of the honest prover for a list of residues: their bits, row after row. -/
def encodeReply (p : ℕ) (l : List ℕ) : List Bool := l.flatMap (BitString.binaryWord (width p))

theorem length_decodeReply (p D : ℕ) (word : List Bool) :
    (decodeReply p D word).length = D + 1 := by
  simp [decodeReply]

theorem lt_of_mem_decodeReply [NeZero p] {D : ℕ} {word : List Bool} {a : ℕ}
    (ha : a ∈ decodeReply p D word) : a < p := by
  obtain ⟨row, -, rfl⟩ := List.mem_map.1 ha
  exact Nat.mod_lt _ (NeZero.pos p)

private theorem lt_two_pow_width {a : ℕ} (hp : a < p) : a < 2 ^ width p :=
  hp.trans (Nat.lt_pow_succ_log_self (by norm_num) p)

/-- The rows of the honest encoding of `l` are the bits of its elements. -/
private theorem listRow_encodeReply {l : List ℕ} (hl : ∀ a ∈ l, a < p) (i : ℕ) :
    BitString.listRow (width p) i (encodeReply p l) =
      if h : i < l.length then BitString.binaryWord (width p) l[i]
      else List.replicate (width p) false := by
  induction l generalizing i with
  | nil =>
    simp [BitString.listRow, encodeReply]
  | cons a l ih =>
    have ha := BitString.length_binaryWord (lt_two_pow_width (hl a List.mem_cons_self))
    have ih := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    cases i with
    | zero =>
      simp [BitString.listRow, encodeReply, List.take_append_of_le_length (le_of_eq ha.symm),
        List.take_of_length_le (le_of_eq ha)]
    | succ i =>
      have := ih i
      simp only [BitString.listRow, encodeReply] at this ⊢
      rw [List.flatMap_cons, Nat.succ_mul, ← Nat.add_comm, ← List.drop_drop,
        List.drop_append_of_le_length (le_of_eq ha.symm), List.drop_of_length_le (le_of_eq ha),
        List.nil_append, this]
      simp

/-- **Decoding inverts the honest encoding** of at most `D + 1` residues, padded with zeros. -/
theorem decodeReply_encodeReply {D : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < p)
    (hlen : l.length ≤ D + 1) :
    decodeReply p D ((encodeReply p l).take (replyLimit p D)) =
      (List.range (D + 1)).map fun i => l.getD i 0 := by
  have hlength : (encodeReply p l).length ≤ replyLimit p D := by
    have : (encodeReply p l).length = l.length * width p := by
      simp only [encodeReply, List.length_flatMap]
      rw [List.map_congr_left fun a ha => BitString.length_binaryWord (lt_two_pow_width (hl a ha)),
        List.map_const', List.sum_replicate, smul_eq_mul]
    rw [this, replyLimit]
    exact Nat.mul_le_mul_right _ hlen
  rw [List.take_of_length_le hlength, decodeReply, BitString.listRows, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, listRow_encodeReply hl]
  split_ifs with hi
  · rw [BitString.boundedBinaryValue_eq, BitString.binaryValue_binaryWord, Nat.min_eq_right,
      Nat.mod_eq_of_lt, List.getD_eq_getElem _ _ hi]
    · exact hl _ (List.getElem_mem hi)
    · exact (hl _ (List.getElem_mem hi)).le.trans (lt_dyadicSize p).le
  · rw [BitString.boundedBinaryValue_eq, List.getD_eq_default _ _ (not_lt.1 hi)]
    have : BitString.binaryValue (List.replicate (width p) false) = 0 := by
      rw [← List.append_nil (List.replicate _ _), BitString.binaryValue_replicate_false_append]
      rfl
    rw [this, Nat.min_zero, Nat.zero_mod]

/-! ### Samples -/

/-- A uniform index in the dyadic range above `p`, reduced modulo `p`. -/
noncomputable def sampleMod (p : ℕ) : ProbComp ℕ := (· % p) <$> sampleDyadicIndex p

theorem lt_of_mem_support_sampleMod [NeZero p] {n : ℕ}
    (hn : n ∈ (ProbComp.eval (sampleMod p)).support) : n < p := by
  rw [sampleMod, ProbComp.eval_map, PMF.mem_support_map_iff] at hn
  obtain ⟨i, -, rfl⟩ := hn
  exact Nat.mod_lt _ (NeZero.pos p)

/-- At most `N / p + 1` numbers below `N` have a given residue modulo `p`. -/
private theorem card_filter_mod_eq_le (N n : ℕ) :
    (Finset.univ.filter fun i : Fin N => n = i.val % p).card ≤ N / p + 1 := by
  calc (Finset.univ.filter fun i : Fin N => n = i.val % p).card
      ≤ (Finset.range (N / p + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun i => i.val / p) (fun i _ => ?_)
          (fun i hi j hj hij => ?_)
        · simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hi hj
          have hij : i.val / p = j.val / p := hij
          apply Fin.ext
          rw [← Nat.div_add_mod i.val p, ← Nat.div_add_mod j.val p, ← hi, ← hj, hij]
    _ = N / p + 1 := Finset.card_range _

/-- **The samples are nearly uniform**: every residue has probability at most `2 / p`. -/
theorem eval_sampleMod_le [NeZero p] (n : ℕ) : ProbComp.eval (sampleMod p) n ≤ 2 / p := by
  have hN : p < dyadicSize p := lt_dyadicSize p
  have hNpos : ((dyadicSize p : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (dyadicSize_pos p).ne'
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.pos p).ne'
  rw [sampleMod, ProbComp.eval_map, eval_sampleDyadicIndex, PMF.map_comp, PMF.map_apply,
    tsum_fintype]
  simp only [Function.comp_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv,
    ENNReal.div_le_iff hNpos (ENNReal.natCast_ne_top _), ENNReal.div_eq_inv_mul, mul_assoc,
    ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hp0)
      (Or.inl (ENNReal.natCast_ne_top p))]
  have hcard := card_filter_mod_eq_le (p := p) (dyadicSize p) n
  have hmul : (dyadicSize p / p + 1) * p ≤ 2 * dyadicSize p := by
    have := Nat.div_mul_le_self (dyadicSize p) p
    nlinarith
  calc ((Finset.univ.filter fun i : Fin (dyadicSize p) => n = i.val % p).card : ℝ≥0∞) * p
      ≤ ((dyadicSize p / p + 1 : ℕ) : ℝ≥0∞) * p := by gcongr
    _ ≤ 2 * dyadicSize p := by exact_mod_cast hmul

/-! ### Polynomial time -/

section PolyTime

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

@[fun_prop]
theorem computableInPolyTime_subMod {p a b : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => subMod (p x) (a x) (b x)) encIn encUnary := by
  unfold subMod
  fun_prop

theorem computableInPolyTime_connectiveMod (o : ArithQBF.Connective) {p a b : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => connectiveMod (p x) o (a x) (b x)) encIn encUnary := by
  cases o <;> simp only [connectiveMod] <;> fun_prop

theorem computableInPolyTime_operatorMod (o : ArithQBF.Operator) {p t a b : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => operatorMod (p x) o (t x) (a x) (b x)) encIn encUnary := by
  cases o <;> simp only [operatorMod] <;> fun_prop

@[fun_prop]
theorem computableInPolyTime_hornerMod {p z : γ → ℕ} {l : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hz : ComputableInPolyTime z encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => hornerMod (p x) (z x) (l x)) encIn encUnary := by
  unfold hornerMod
  refine foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (const 0) ⟨by fun_prop, by fun_prop, inferInstance, inferInstance⟩
    (growth := fun x => p x + 1) ⟨(polyBounded hp).add (.const 1), fun x acc a _ => ?_⟩
  simp only [encUnary_apply, List.length_replicate]
  have := Nat.mod_lt (a + z x * acc) (by omega : 0 < p x - 1 + 1)
  omega

@[fun_prop]
theorem computableInPolyTime_lookupPt {pt : γ → List (ℕ × ℕ)} {w : γ → ℕ}
    (hpt : ComputableInPolyTime pt encIn (encList (encPair encNat encUnary)))
    (hw : ComputableInPolyTime w encIn encNat) :
    ComputableInPolyTime (fun x => lookupPt (pt x) (w x)) encIn encUnary := by
  unfold lookupPt
  have htest : ComputableInPolyTime (fun q : γ × (ℕ × ℕ) => q.2.1 == w q.1)
      (encPair encIn (encPair encNat encUnary)) encBool := by fun_prop
  exact optionElimWithInput (findWithInput hpt htest) (const 0) (by fun_prop)

@[fun_prop]
theorem computableInPolyTime_normPt {p : γ → ℕ} {xs : γ → List ℕ}
    {pt : γ → List (ℕ × ℕ)} (hp : ComputableInPolyTime p encIn encUnary)
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hpt : ComputableInPolyTime pt encIn (encList (encPair encNat encUnary))) :
    ComputableInPolyTime (fun x => normPt (p x) (xs x) (pt x)) encIn
      (encList (encPair encNat encUnary)) := by
  unfold normPt
  fun_prop

@[fun_prop]
theorem computableInPolyTime_updatePt {p : γ → ℕ} {xs : γ → List ℕ}
    {pt : γ → List (ℕ × ℕ)} {v z : γ → ℕ} (hp : ComputableInPolyTime p encIn encUnary)
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hpt : ComputableInPolyTime pt encIn (encList (encPair encNat encUnary)))
    (hv : ComputableInPolyTime v encIn encNat)
    (hz : ComputableInPolyTime z encIn encUnary) :
    ComputableInPolyTime (fun x => updatePt (p x) (xs x) (pt x) (v x) (z x)) encIn
      (encList (encPair encNat encUnary)) := by
  unfold updatePt
  fun_prop

@[fun_prop]
theorem computableInPolyTime_width {p : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary) :
    ComputableInPolyTime (fun x => width (p x)) encIn encUnary := by
  unfold width
  fun_prop

@[fun_prop]
theorem computableInPolyTime_replyLimit {p D : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary) :
    ComputableInPolyTime (fun x => replyLimit (p x) (D x)) encIn encUnary := by
  unfold replyLimit
  fun_prop

@[fun_prop]
theorem computableInPolyTime_decodeReply {p D : γ → ℕ} {word : γ → List Bool}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hword : ComputableInPolyTime word encIn encBits) :
    ComputableInPolyTime (fun x => decodeReply (p x) (D x) (word x)) encIn
      (encList encUnary) := by
  unfold decodeReply
  fun_prop

/-- The samples are strict PPT in a unary modulus. -/
theorem isPPTOn_sampleMod {p : γ → ℕ} (hp : ComputableInPolyTime p encIn encUnary) :
    IsPPTOn encIn encUnary (fun x => sampleMod (p x)) := by
  unfold sampleMod
  exact IsPPTOn.map_with (f := fun x i => i % p x)
    (isPPTOn_sampleDyadicIndex hp) (by fun_prop)

end PolyTime

end Cslib.Complexity.QBFProtocol
