/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.MultiNPHard.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Data.List.GetD

/-!
# The Set Cover to Multi-MCSP reduction runs in polynomial time

`MultiMCSP.Reduction.computableInPolyTime_reduce`: the reduction `MultiMCSP.Reduction.reduce` of
Ilango, Loff and Oliveira [IlangoLoffOliveira2020, §4.2, pp. 22:20–22:21] is computable in
polynomial time, from the encoding of a `GapSetCover` instance followed by the random string to
`MultiMCSP.encInstance`.

The proof writes the encoded fields of the output instance with list operations: each table entry
in closed form from the gate numbering of `Window.Gate.equivFin`, and the threshold's count of
distinct non-input gate functions by erasing duplicate rows that are not input projections. Every
list has polynomial length because `2 ^ arity S ≤ 64 (N + t + 4) ^ 6`
(`MultiMCSP.Reduction.two_pow_arity_le`).

## Main results

* `Cslib.MultiMCSP.Reduction.computableInPolyTime_reduce`: the reduction runs in polynomial time.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib

open Circuits Finset Complexity Turing.MultiTapeTM

namespace MultiMCSP.Reduction

/-! ### The encoded fields in closed form -/

/-- Entry `z` of the truth table of gate `j` of the template for `S` and the random string `r`,
written with arithmetic on `j` and `z`, in the gate order of `Window.Gate.equivFin`. -/
private def entry (S : SetSystem) (r : List Bool) (j z : ℕ) : Bool :=
  let p := arity S
  if j < p then !z.testBit j
  else if j = p then false
  else if j < p + 1 + 2 ^ p * p then
    (List.range ((j - (p + 1)) % p + 1)).all fun b =>
      z.testBit b == ((j - (p + 1)) / p).testBit b
  else if j < Window.gateCount p S.sets.length then
    decide (z ≤ (j - (p + 1 + 2 ^ p * p)) % 2 ^ p) &&
      decide (S.ground.getD (z % S.ground.length) 0 ∈
        S.sets.getD ((j - (p + 1 + 2 ^ p * p)) / 2 ^ p) []) &&
      r.getD z false
  else r.getD z false

/-- The truth table of gate `j`, as a list of `2 ^ p` bits. -/
private def row (S : SetSystem) (r : List Bool) (j : ℕ) : List Bool :=
  (List.range (2 ^ arity S)).map (entry S r j)

/-- The truth table of the projection to input `i`, on `p` inputs. -/
private def projRow (p i : ℕ) : List Bool :=
  (List.range (2 ^ p)).map fun z => z.testBit i

/-- The number of distinct rows of the template that are not input projections. -/
private def nonInputCount (S : SetSystem) (r : List Bool) : ℕ :=
  (((List.range (Window.gateCount (arity S) S.sets.length)).map (row S r)).filter
    (fun R => !(List.range (arity S)).any fun i => projRow (arity S) i == R)).eraseDupsBy
    (fun a b => decide (a = b)) |>.length

/-- The fields `(n, m, s, table bits)` that `encInstance` writes for `reduce`. -/
private def fields (x : (SetSystem × ℕ) × List Bool) : ℕ × ℕ × ℕ × List Bool :=
  if x.1.1.ground.isEmpty then (1, 1, 1, [false, true])
  else (arity x.1.1, Window.gateCount (arity x.1.1) x.1.1.sets.length + 1,
    nonInputCount x.1.1 x.2 + min x.1.2 x.1.1.sets.length,
    (List.range (Window.gateCount (arity x.1.1) x.1.1.sets.length + 1)).flatMap (row x.1.1 x.2))

/-! ### The closed form is the reduction -/

section Bridge

variable {S : SetSystem} {r : List Bool}

/-- The window sets of the template for `S`. -/
private abbrev windows (S : SetSystem) : Fin S.sets.length → Finset (Fin (2 ^ arity S)) :=
  fun i => Window.lift (arity S) S.ground.length (residues S i)

/-- The table of the random string `r`. -/
private abbrev tableOf (S : SetSystem) (r : List Bool) : Fin (2 ^ arity S) → Bool :=
  fun y => r.getD y false

private theorem entry_equivFin (hS : S.ground ≠ []) (κ : Window.Gate (arity S) S.sets.length)
    (z : Fin (2 ^ arity S)) :
    entry S r (Window.Gate.equivFin _ _ κ) z =
      Window.value (windows S) (tableOf S r) κ ((BitString.equivFin _).symm z) := by
  have hN : 0 < S.ground.length := List.length_pos_iff.mpr hS
  have hp : 0 < arity S := by have := eighteen_le_arity S; omega
  cases κ with
  | neg i =>
    simp [entry, Window.value_neg, BitString.equivFin_symm_apply, i.isLt]
  | zero =>
    simp [entry]
  | grid y k =>
    have hk : ((k : ℕ) + arity S * y) % arity S = k := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
    have hy : ((k : ℕ) + arity S * y) / arity S = y := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt k.isLt, zero_add]
    have hlt : arity S + (1 + ((k : ℕ) + arity S * y)) <
        arity S + 1 + 2 ^ arity S * arity S := by
      have := y.isLt
      have := k.isLt
      have : arity S * y + arity S ≤ 2 ^ arity S * arity S := by
        rw [Nat.mul_comm (2 ^ _)]
        nlinarith
      omega
    rw [Window.value_grid]
    simp only [entry, Window.Gate.val_equivFin_grid]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hlt,
      show arity S + (1 + ((k : ℕ) + arity S * y)) - (arity S + 1) = k + arity S * y by omega,
      hk, hy]
    simp only [BitString.equivFin_symm_apply]
    have := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h b hb
      exact h b (Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hb))
    · intro h b hb
      exact h ⟨b, by omega⟩ (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hb))
  | window i y =>
    have hy : ((y : ℕ) + 2 ^ arity S * i) % 2 ^ arity S = y := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
    have hi : ((y : ℕ) + 2 ^ arity S * i) / 2 ^ arity S = i := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt y.isLt, zero_add]
    have hlt : arity S + (1 + (2 ^ arity S * arity S + ((y : ℕ) + 2 ^ arity S * i))) <
        Window.gateCount (arity S) S.sets.length := by
      rw [Window.gateCount_eq]
      have := y.isLt
      have := i.isLt
      have : (y : ℕ) + 2 ^ arity S * i < S.sets.length * 2 ^ arity S := by
        rw [Nat.mul_comm S.sets.length]
        nlinarith
      omega
    rw [Window.value_window]
    simp only [entry, Window.Gate.val_equivFin_window]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hlt,
      show arity S + (1 + (2 ^ arity S * arity S + ((y : ℕ) + 2 ^ arity S * i))) -
        (arity S + 1 + 2 ^ arity S * arity S) = y + 2 ^ arity S * i by omega, hy, hi]
    simp only [Equiv.apply_symm_apply, Window.mem_lift, mem_residues]
    have hmod : (z : ℕ) % S.ground.length < S.ground.length := Nat.mod_lt _ hN
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.getD_eq_getElem _ _ hmod,
      List.getD_eq_getElem _ _ i.isLt, hmod, exists_true_left, tableOf, Fin.le_iff_val_le_val,
      Fin.getElem_fin, and_assoc]

/-- The last row of the table is the random string. -/
private theorem entry_gateCount (z : ℕ) :
    entry S r (Window.gateCount (arity S) S.sets.length) z = r.getD z false := by
  have := Window.gateCount_eq (arity S) S.sets.length
  simp only [entry]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- A truth table as a list of `2 ^ p` bits. -/
private def tableList (p : ℕ) (f : (Fin p → Bool) → Bool) : List Bool :=
  List.ofFn (MCSP.truthTable p f)

private theorem tableList_injective (p : ℕ) : Function.Injective (tableList p) :=
  fun _ _ h => (MCSP.truthTable p).injective (List.ofFn_injective h)

private theorem tableList_eq {p : ℕ} {f : (Fin p → Bool) → Bool} {g : ℕ → Bool}
    (h : ∀ z : Fin (2 ^ p), f ((BitString.equivFin p).symm z) = g z) :
    tableList p f = (List.range (2 ^ p)).map g := by
  refine List.ext_getElem (by simp [tableList]) fun n h₁ _ => ?_
  simp only [tableList, List.getElem_ofFn, MCSP.truthTable_apply, List.getElem_map,
    List.getElem_range]
  exact h ⟨n, by simpa [tableList] using h₁⟩

private theorem tableList_template (hS : S.ground ≠ [])
    (j : Fin (Window.gateCount (arity S) S.sets.length)) :
    tableList (arity S) (fun x => Window.template (windows S) (tableOf S r) x j) = row S r j := by
  refine tableList_eq fun z => ?_
  obtain ⟨κ, rfl⟩ := (Window.Gate.equivFin (arity S) S.sets.length).surjective j
  rw [Window.template_equivFin, entry_equivFin hS]

private theorem tableList_proj (i : Fin (arity S)) :
    tableList (arity S) (fun x => x i) = projRow (arity S) i :=
  tableList_eq fun z => by simp [BitString.equivFin_symm_apply]

/-- **The threshold's count.** The distinct non-input gate functions of the template are the
distinct rows that are not input projections. -/
private theorem card_nonInputComponents (hS : S.ground ≠ []) :
    #(nonInputComponents (Window.template (windows S) (tableOf S r))) = nonInputCount S r := by
  classical
  set L := ((List.range (Window.gateCount (arity S) S.sets.length)).map (row S r)).filter
    (fun R => !(List.range (arity S)).any fun i => projRow (arity S) i == R) with hL
  have himage : (nonInputComponents (Window.template (windows S) (tableOf S r))).image
      (tableList (arity S)) = L.toFinset := by
    ext R
    simp only [mem_image, mem_nonInputComponents, List.mem_toFinset, hL, List.mem_filter,
      List.mem_map, List.mem_range, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    constructor
    · rintro ⟨h, ⟨⟨j, rfl⟩, hproj⟩, rfl⟩
      refine ⟨⟨j, j.isLt, (tableList_template hS j).symm⟩, fun i hi heq => hproj ⟨i, hi⟩ ?_⟩
      rw [show projRow (arity S) i = projRow (arity S) (⟨i, hi⟩ : Fin (arity S)) from rfl,
        ← tableList_proj] at heq
      exact (tableList_injective _ heq).symm
    · rintro ⟨⟨j, hj, rfl⟩, hproj⟩
      refine ⟨_, ⟨⟨⟨j, hj⟩, rfl⟩, fun i heq => hproj i i.isLt ?_⟩, tableList_template hS ⟨j, hj⟩⟩
      rw [← tableList_proj, ← tableList_template hS ⟨j, hj⟩, heq]
  rw [← card_image_of_injective _ (tableList_injective _), himage, nonInputCount, ← hL,
    ← List.toFinset_card_of_nodup (List.nodup_eraseDupsBy_eq L)]
  congr 1
  ext R
  simp [List.mem_eraseDupsBy_eq]

/-- **The table bits.** The template's rows followed by the random string. -/
private theorem tableBits_ofTable (hS : S.ground ≠ []) (k : ℕ) :
    (ofTable S k (tableOf S r)).tableBits =
      (List.range (Window.gateCount (arity S) S.sets.length + 1)).flatMap (row S r) := by
  rw [Instance.tableBits_eq_flatten, List.flatMap_def, List.ofFn_eq_map]
  congr 1
  refine List.ext_getElem (by simp [ofTable, Instance.ofFunction]) fun n h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  have hn : n < Window.gateCount (arity S) S.sets.length + 1 := by simpa using h₂
  change tableList _ (fun x => Fin.append _ (single (Window.tableFun (tableOf S r)) x) _) = _
  obtain h | h := Nat.lt_succ_iff_lt_or_eq.mp hn
  · change tableList _ (fun x => Fin.append (Window.template (windows S) (tableOf S r) x)
      (single (Window.tableFun (tableOf S r)) x) (Fin.castSucc ⟨n, h⟩)) = _
    rw [← tableList_template hS ⟨n, h⟩]
    congr 1
    funext x
    exact Fin.append_left _ _ _
  · subst h
    change tableList _ (fun x => Fin.append (Window.template (windows S) (tableOf S r) x)
      (single (Window.tableFun (tableOf S r)) x) (Fin.last _)) = _
    refine tableList_eq fun z => ?_
    rw [entry_gateCount, show Fin.last (Window.gateCount (arity S) S.sets.length) =
      Fin.natAdd _ (0 : Fin 1) from rfl, Fin.append_right]
    simp [Window.tableFun_apply]

/-- **The encoding of the reduction**, field by field. -/
private theorem encInstance_reduce (x : (SetSystem × ℕ) × List Bool) :
    encInstance (reduce x) = encUnaryFields (fields x) := by
  obtain ⟨⟨S, k⟩, r⟩ := x
  rw [encInstance_apply]
  by_cases hS : S.ground = []
  · rw [reduce_of_ground_eq_nil hS]
    simp only [fields, hS, List.isEmpty_nil, ite_true]
    rfl
  · rw [reduce_of_ground_ne_nil hS]
    have hne : S.ground.isEmpty = false := by simpa using hS
    simp only [fields, hne, Bool.false_eq_true, ite_false]
    rw [← tableBits_ofTable (r := r) hS k]
    change encUnaryFields (_, _, (ofTable S k (tableOf S r)).threshold, _) = _
    exact congrArg encUnaryFields (Prod.ext rfl (Prod.ext rfl (Prod.ext
      (congrArg (· + min k S.sets.length) (card_nonInputComponents (r := r) hS)) rfl)))

end Bridge

/-! ### Polynomial time -/

section PolyTime

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool} {sys : γ → SetSystem} {bits : γ → List Bool}

private theorem polyTime_bound (hsys : ComputableInPolyTime sys encIn encSetSystem) :
    ComputableInPolyTime (fun c => bound (sys c)) encIn encUnary := by
  unfold bound
  exact unary_add' (unary_add'
    ((length_list _).comp (computableInPolyTime_setSystemGround.comp hsys))
    ((length_list _).comp (computableInPolyTime_setSystemSets.comp hsys))) (const 4)

private theorem polyTime_arity (hsys : ComputableInPolyTime sys encIn encSetSystem) :
    ComputableInPolyTime (fun c => arity (sys c)) encIn encUnary := by
  unfold arity
  exact unary_mul' (const 6) (binary_size.comp (unary_to_binary.comp (polyTime_bound hsys)))

private theorem polyTime_twoPowArity (hsys : ComputableInPolyTime sys encIn encSetSystem) :
    ComputableInPolyTime (fun c => 2 ^ arity (sys c)) encIn encUnary :=
  binary_to_unary_bounded (binary_two_pow.comp (polyTime_arity hsys))
    (unary_mul' (const 64) ((unary_pow 6).comp (polyTime_bound hsys)))
    fun c => two_pow_arity_le (sys c)

private theorem polyTime_gateCount (hsys : ComputableInPolyTime sys encIn encSetSystem) :
    ComputableInPolyTime (fun c => Window.gateCount (arity (sys c)) (sys c).sets.length)
      encIn encUnary := by
  simp only [Window.gateCount_eq]
  have hp := polyTime_arity hsys
  have hq := polyTime_twoPowArity hsys
  exact unary_add' hp (unary_add' (const 1) (unary_add' (unary_mul' hq hp)
    (unary_mul' ((length_list _).comp (computableInPolyTime_setSystemSets.comp hsys)) hq)))

private theorem polyTime_entry {j z : γ → ℕ} (hsys : ComputableInPolyTime sys encIn encSetSystem)
    (hbits : ComputableInPolyTime bits encIn encBits)
    (hj : ComputableInPolyTime j encIn encUnary) (hz : ComputableInPolyTime z encIn encUnary) :
    ComputableInPolyTime (fun c => entry (sys c) (bits c) (j c) (z c)) encIn encBool := by
  have hp := polyTime_arity hsys
  have hq := polyTime_twoPowArity hsys
  have hG := polyTime_gateCount hsys
  have hground := computableInPolyTime_setSystemGround.comp hsys
  have hsets := computableInPolyTime_setSystemSets.comp hsys
  have hzb := unary_to_binary.comp hz
  have hr := bitsGetDWithInput hbits hz false
  unfold entry
  dsimp only
  refine ite_decide (unary_lt' hj hp) (bool_not.comp (binary_testBit hzb hj)) ?_
  refine ite_decide (unary_eq' hj hp) (const false) ?_
  refine ite_decide (unary_lt' hj (unary_add' (unary_add' hp (const 1)) (unary_mul' hq hp)))
    ?_ ?_
  · have hd := unary_sub' hj (unary_add' hp (const 1))
    refine allWithInput (unary_range' (unary_add' (unary_mod' hd hp) (const 1))) ?_
    exact beq (binary_testBit (hzb.comp (fst _ _)) (snd _ _))
      (binary_testBit (unary_to_binary.comp ((unary_div' hd hp).comp (fst _ _))) (snd _ _))
  refine ite_decide (unary_lt' hj hG) ?_ hr
  have hd := unary_sub' hj (unary_add' (unary_add' hp (const 1)) (unary_mul' hq hp))
  refine bool_and' (bool_and' (unary_le' hz (unary_mod' hd hq)) ?_) hr
  exact decide_mem (listGetDWithInput hsets (unary_div' hd hq) [])
    (listGetDWithInput hground (unary_mod' hz ((length_list _).comp hground)) 0)

private theorem polyTime_row {j : γ → ℕ} (hsys : ComputableInPolyTime sys encIn encSetSystem)
    (hbits : ComputableInPolyTime bits encIn encBits)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun c => row (sys c) (bits c) (j c)) encIn encBits := by
  unfold row
  exact mapToBitsWithInput (unary_range' (polyTime_twoPowArity hsys))
    (polyTime_entry (hsys.comp (fst _ _)) (hbits.comp (fst _ _)) (hj.comp (fst _ _)) (snd _ _))

private theorem polyTime_projRow {i : γ → ℕ} (hsys : ComputableInPolyTime sys encIn encSetSystem)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun c => projRow (arity (sys c)) (i c)) encIn encBits := by
  unfold projRow
  exact mapToBitsWithInput (unary_range' (polyTime_twoPowArity hsys))
    (binary_testBit (unary_to_binary.comp (snd _ _)) (hi.comp (fst _ _)))

private theorem polyTime_nonInputCount (hsys : ComputableInPolyTime sys encIn encSetSystem)
    (hbits : ComputableInPolyTime bits encIn encBits) :
    ComputableInPolyTime (fun c => nonInputCount (sys c) (bits c)) encIn encUnary := by
  unfold nonInputCount
  have hrows : ComputableInPolyTime
      (fun c => (List.range (Window.gateCount (arity (sys c)) (sys c).sets.length)).map
        (row (sys c) (bits c))) encIn (encList encBits) :=
    mapWithInput (unary_range' (polyTime_gateCount hsys))
      (polyTime_row (hsys.comp (fst encIn encUnary)) (hbits.comp (fst encIn encUnary))
        (snd encIn encUnary))
  have hproj : ComputableInPolyTime
      (fun q : (γ × List Bool) × ℕ => projRow (arity (sys q.1.1)) q.2 == q.1.2)
      (encPair (encPair encIn encBits) encUnary) encBool :=
    beq (polyTime_projRow (hsys.comp ((fst encIn encBits).comp (fst _ encUnary))) (snd _ _))
      ((snd encIn encBits).comp (fst _ encUnary))
  have htest : ComputableInPolyTime
      (fun q : γ × List Bool =>
        !(List.range (arity (sys q.1))).any fun i => projRow (arity (sys q.1)) i == q.2)
      (encPair encIn encBits) encBool :=
    bool_not.comp (anyWithInput (unary_range' (polyTime_arity (hsys.comp (fst encIn encBits))))
      hproj)
  have hfilt := filterWithInput
    (test := fun c R => !(List.range (arity (sys c))).any fun i => projRow (arity (sys c)) i == R)
    hrows htest
  have heq : ComputableInPolyTime
      (fun q : (γ × List Bool) × List Bool => decide (q.1.2 = q.2))
      (encPair (encPair encIn encBits) encBits) encBool :=
    decide_eq' ((snd encIn encBits).comp (fst _ encBits)) (snd _ encBits)
  exact (length_list _).comp
    (eraseDupsByWithInput (r := fun _ a b => decide (a = b)) hfilt heq)

private theorem polyTime_fields :
    ComputableInPolyTime fields (encPair encSetCover encBits) encUnaryFields := by
  have hsys : ComputableInPolyTime (fun x : (SetSystem × ℕ) × List Bool => x.1.1)
      (encPair encSetCover encBits) encSetSystem := (fst _ _).comp (fst _ _)
  have hk : ComputableInPolyTime (fun x : (SetSystem × ℕ) × List Bool => x.1.2)
      (encPair encSetCover encBits) encNat := (snd _ _).comp (fst _ _)
  have hbits : ComputableInPolyTime (fun x : (SetSystem × ℕ) × List Bool => x.2)
      (encPair encSetCover encBits) encBits := snd _ _
  have hG := polyTime_gateCount hsys
  have hmin : ComputableInPolyTime
      (fun x : (SetSystem × ℕ) × List Bool => min x.1.2 x.1.1.sets.length)
      (encPair encSetCover encBits) encUnary :=
    (binary_min_unary' ((length_list _).comp (computableInPolyTime_setSystemSets.comp hsys))
      hk).of_enc_eq fun x => congrArg encUnary (min_comm _ _)
  unfold fields
  refine ite' ((listIsEmpty (encA := encNat) (encL := encList encNat)).comp
    (computableInPolyTime_setSystemGround.comp hsys)) (const _) ?_
  exact (polyTime_arity hsys).prod ((unary_add' hG (const 1)).prod
    ((unary_add' (polyTime_nonInputCount hsys hbits) hmin).prod
      (flatMapToBitsWithInput (unary_range' (unary_add' hG (const 1)))
        (polyTime_row (hsys.comp (fst _ _)) (hbits.comp (fst _ _)) (snd _ _)))))

/-- **The reduction runs in polynomial time**, from a `GapSetCover` instance followed by the random
string to the encoded Multi-MCSP instance. -/
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce (encPair encSetCover encBits) encInstance :=
  polyTime_fields.of_enc_eq encInstance_reduce

end PolyTime

end MultiMCSP.Reduction

end Cslib
