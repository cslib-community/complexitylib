/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawController
public import Complexity.Computability.TreeEval.Reader.Cert.Residue

/-!
# Native streamed updates of the flat register bank

Indexed bank updates are streamed with a binary index and an output prefix. No list of indices
is materialized. The budget charges the possible field width of every output cell; the raw
controller's padding guard will bound that charge by the already encoded input bank.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

open Turing MultiTapeTM ComputableInSpace Reader

private abbrev BankPar := (ℕ × ℕ × ℕ × ℕ) × List ℕ × Bool × Bool
private abbrev encBankPar : BankPar ↪ List Bool :=
  encPair (encPair encNat (encPair encNat (encPair encNat encNat)))
    (encPair (encList encNat) (encPair encBool encBool))
private abbrev encBankAcc : (ℕ × List ℕ) ↪ List Bool := encPair encNat (encList encNat)

private def bankCell (q : BankPar) (k v : ℕ) : ℕ :=
  if q.1.1 = 0 then v else
    if k / q.1.2.1 = q.1.2.2.1 then
      q.1.1 + if q.2.2.1 then
        addMod q.1.1 v (if q.2.2.2 then
          negMod q.1.1 (mulMod q.1.1 q.1.2.2.2 (q.2.1.getD (k % q.1.2.1) 0))
        else mulMod q.1.1 q.1.2.2.2 (q.2.1.getD (k % q.1.2.1) 0))
      else mulMod q.1.1 q.1.2.2.2 v
    else v

private def bankFoldStep (q : BankPar) (st : ℕ × List ℕ) (v : ℕ) : ℕ × List ℕ :=
  (st.1 + 1, st.2 ++ [bankCell q st.1 v])

private theorem foldl_bankFoldStep (q : BankPar) (l : List ℕ) (j : ℕ) (out : List ℕ) :
    l.foldl (bankFoldStep q) (j, out) =
      (j + l.length, out ++ l.mapIdx (fun k v => bankCell q (j + k) v)) := by
  induction l generalizing j out with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, bankFoldStep, ih]
    simp only [List.length_cons, List.mapIdx_cons]
    have hf : (fun k v => bankCell q (j + 1 + k) v) =
        (fun k v => bankCell q (j + (k + 1)) v) := by
      funext k v
      congr 1
      omega
    rw [hf]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

private theorem bankCell_length (q : BankPar) (k v : ℕ) :
    (encNat (bankCell q k v)).length ≤ (encNat v).length +
      2 * (encNat q.1.1).length + 1 := by
  by_cases hp : q.1.1 = 0
  · simp [bankCell, hp]
  by_cases hk : k / q.1.2.1 = q.1.2.2.1
  · have hres : bankCell q k v < q.1.1 + q.1.1 := by
      simp only [bankCell, hp, ↓reduceIte, hk]
      split_ifs <;> simp only [addMod, mulMod] <;>
        exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)) _
    have hb := length_encNat_mono hres.le
    have ha := length_encNat_add_le_add q.1.1 q.1.1
    omega
  · simp only [bankCell, hp, hk, ↓reduceIte]
    omega

private theorem length_bankMap (q : BankPar) (l : List ℕ) (j : ℕ) :
    (encList encNat (l.mapIdx (fun k v => bankCell q (j + k) v))).length ≤
      (encList encNat l).length + l.length * (4 * (encNat q.1.1).length + 2) := by
  induction l generalizing j with
  | nil => simp
  | cons v l ih =>
    have hc := bankCell_length q j v
    have ht := ih (j + 1)
    have hf : (fun k v => bankCell q (j + (k + 1)) v) =
        (fun k v => bankCell q (j + 1 + k) v) := by
      funext k v
      congr 1
      omega
    simp only [List.mapIdx_cons, hf, encList_cons, List.length_append, length_frame,
      List.length_cons, Nat.add_zero]
    nlinarith

private theorem bankFoldStep_inSpace :
    ComputableInSpace (fun a : (BankPar × (ℕ × List ℕ)) × ℕ =>
      bankFoldStep a.1.1 a.1.2 a.2)
      (encPair (encPair encBankPar encBankAcc) encNat) encBankAcc
      (fun a => (encPair (encPair encBankPar encBankAcc) encNat a).length) := by
  have hqa := fst (encPair encBankPar encBankAcc) encNat
  have hq := fst' hqa
  have hst := snd' hqa
  have hj := fst' hst
  have hout := snd' hst
  have hv := snd (encPair encBankPar encBankAcc) encNat
  have hpars := fst' hq
  have hp := fst' hpars
  have hrest := snd' hpars
  have hr := fst' hrest
  have ht := fst' (snd' hrest)
  have hc := snd' (snd' hrest)
  have hvals := fst' (snd' hq)
  have hflags := snd' (snd' hq)
  have huse := fst' hflags
  have hsub := snd' hflags
  have hval := budget_comp_lin getD (linear_mul 8)
    (budget_prod hvals (budget_natMod hj hr))
  have hprod := budget_comp_linear mulMod_inSpace
    (budget_prod hp (budget_prod hc hval))
  have hneg := budget_comp_linear negMod_inSpace (budget_prod hp hprod)
  have hadd := budget_comp_linear addMod_inSpace
    (budget_prod hp (budget_prod hv (budget_ite hsub hneg hprod)))
  have hscale := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hc hv))
  have hupdated := budget_natAdd hp (budget_ite huse hadd hscale)
  have hcell := budget_ite (budget_natIsZero hp) hv
    (budget_ite (budget_natEq (budget_natDiv hj hr) ht) hupdated hv)
  refine (budget_prod (budget_natSucc hj) (budget_snoc hout hcell)).of_enc_eq ?_
  intro a
  by_cases hp : a.1.1.1.1 = 0 <;>
    by_cases hk : a.1.2.1 / a.1.1.1.2.1 = a.1.1.1.2.2.1 <;>
      simp [bankFoldStep, bankCell, hp, hk]

/-- A streamed indexed update charges only the input and the possible field width per cell.
The zero-modulus branch retains the input bank, so malformed parameters do not expand cells. -/
private def bankUpdateSpace (q : BankPar × List ℕ) : ℕ :=
  (encPair encBankPar (encList encNat) q).length +
    q.2.length * ((encNat q.1.1.1).length + 1) + 1

private theorem bankMap_inSpace :
    ComputableInSpace (fun q : BankPar × List ℕ => q.2.mapIdx (bankCell q.1))
      (encPair encBankPar (encList encNat)) (encList encNat) bankUpdateSpace := by
  let encIn := encPair encBankPar (encList encNat)
  have hpar := fst encBankPar (encList encNat)
  have hlist := snd encBankPar (encList encNat)
  have hinit : ComputableInSpace (fun _ : BankPar × List ℕ => (0, ([] : List ℕ)))
      encIn encBankAcc (fun q => (encIn q).length) := budget_const (0, []) (.refl _)
  have hstate (q : BankPar × List ℕ) (i : ℕ) (hi : i ≤ q.2.length) :
      (encBankAcc ((q.2.take i).foldl (bankFoldStep q.1) (0, []))).length ≤
        16 * bankUpdateSpace q := by
    rw [foldl_bankFoldStep]
    have hc := length_encNat_le_self (q.2.take i).length
    have hl := length_bankMap q.1 (q.2.take i) 0
    have htake := length_encList_sublist encNat (List.take_sublist i q.2)
    have hn := length_le_length_encList encNat q.2
    have hmul := Nat.mul_le_mul_right (4 * (encNat q.1.1.1).length + 2)
      (List.length_take_le i q.2)
    simp only [Nat.zero_add, List.nil_append, encBankAcc, length_encPair] at *
    dsimp only [bankUpdateSpace]
    simp only [length_encPair]
    nlinarith
  have hspace (q : BankPar × List ℕ) (i : ℕ) (hi : i < q.2.length) :
      (encPair (encPair encBankPar encBankAcc) encNat
        ((q.1, (q.2.take i).foldl (bankFoldStep q.1) (0, [])), q.2[i])).length ≤
          128 * bankUpdateSpace q := by
    have hs := hstate q i hi.le
    have hv := length_le_encList_of_mem encNat (List.getElem_mem hi)
    change (encNat q.2[i]).length ≤ (encList encNat q.2).length at hv
    simp only [length_encPair]
    dsimp only [bankUpdateSpace] at hs ⊢
    simp only [length_encPair] at hs ⊢
    omega
  have hfold := ComputableInSpace.foldlWith hpar hlist hinit bankFoldStep_inSpace hspace hstate
  refine (snd' hfold).weaken ?_ |>.of_enc_eq ?_
  · refine .of_le_linear 256 256 fun q => ?_
    have hb : (encIn q).length ≤ bankUpdateSpace q := by
      dsimp only [bankUpdateSpace, encIn]
      omega
    have hp := length_le_encPair_left encBankPar (encList encNat) q
    have hl := length_le_encPair_right encBankPar (encList encNat) q
    dsimp only [encIn] at hb ⊢
    omega
  · intro q
    rw [foldl_bankFoldStep]
    simp only [Nat.zero_add, List.nil_append]

/-- Padding each cell by the modulus pays its field width in the actual bank encoding. -/
theorem padded_width_le_encoding (p : ℕ) (bank : List ℕ)
    (hpad : ∀ v ∈ bank, p ≤ v) :
    bank.length * (encNat p).length ≤ (encList encNat bank).length := by
  induction bank with
  | nil => simp
  | cons v bank ih =>
    have hv := length_encNat_mono (hpad v List.mem_cons_self)
    have ht := ih (fun v hv => hpad v (List.mem_cons_of_mem _ hv))
    simp only [List.length_cons, encList_cons, List.length_append, length_frame]
    nlinarith

private def paddingStep (p : ℕ) (good : Bool) (v : ℕ) : Bool :=
  good && decide (p ≤ v)

private theorem foldl_paddingStep (p : ℕ) (l : List ℕ) (good : Bool) :
    l.foldl (paddingStep p) good = (good && l.all (fun v => decide (p ≤ v))) := by
  induction l generalizing good with
  | nil => simp
  | cons v l ih => simp [List.foldl_cons, paddingStep, ih, Bool.and_assoc]

private theorem padding_inSpace :
    ComputableInSpace (fun q : BankPar × List ℕ =>
      q.2.all (fun v => decide (q.1.1.1 ≤ v)))
      (encPair encBankPar (encList encNat)) encBool
      (fun q => (encPair encBankPar (encList encNat) q).length) := by
  let encIn := encPair encBankPar (encList encNat)
  have hpar := fst' (fst' (fst encBankPar (encList encNat)))
  have hlist := snd encBankPar (encList encNat)
  have hinit : ComputableInSpace (fun _ : BankPar × List ℕ => true) encIn encBool
      (fun q => (encIn q).length) := budget_const true (.refl _)
  have hstep : ComputableInSpace
      (fun q : (ℕ × Bool) × ℕ => paddingStep q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encBool) encNat) encBool
      (fun q => (encPair (encPair encNat encBool) encNat q).length) := by
    have hp := fst' (fst (encPair encNat encBool) encNat)
    have hg := snd' (fst (encPair encNat encBool) encNat)
    have hv := snd (encPair encNat encBool) encNat
    have hle := budget_finite (encC := encBool) Bool.not (budget_natLt hv hp)
    refine (budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 && q.2)
      (budget_prod hg hle)).of_enc_eq ?_
    intro q
    by_cases h : q.1.1 ≤ q.2
    · simp [paddingStep, h, show ¬q.2 < q.1.1 by omega]
    · simp [paddingStep, h, show q.2 < q.1.1 by omega]
  have hp (q : BankPar × List ℕ) : (encNat q.1.1.1).length ≤ (encIn q).length := by
    simp only [encIn, encBankPar, length_encPair]
    omega
  have hl (q : BankPar × List ℕ) : (encList encNat q.2).length ≤ (encIn q).length :=
    length_le_encPair_right encBankPar (encList encNat) q
  have hspace (q : BankPar × List ℕ) (i : ℕ) (hi : i < q.2.length) :
      (encPair (encPair encNat encBool) encNat
        ((q.1.1.1, (q.2.take i).foldl (paddingStep q.1.1.1) true), q.2[i])).length ≤
          8 * ((encIn q).length + 1) := by
    have hv := length_le_encList_of_mem encNat (List.getElem_mem hi)
    have hb := hp q
    have hc := hl q
    simp only [length_encPair, encBool_apply, List.length_singleton]
    omega
  have hstate (q : BankPar × List ℕ) (i : ℕ) (hi : i ≤ q.2.length) :
      (encBool ((q.2.take i).foldl (paddingStep q.1.1.1) true)).length ≤ 1 := by simp
  have hfold := ComputableInSpace.foldlWith hpar hlist hinit hstep hspace hstate
  refine hfold.weaken ?_ |>.of_enc_eq ?_
  · refine .of_le_linear 32 32 fun q => ?_
    have hb := hp q
    have hc := hl q
    dsimp only [encIn] at hb hc ⊢
    omega
  · intro q
    rw [foldl_paddingStep]
    simp

private def checkedBankMap (q : BankPar × List ℕ) : List ℕ :=
  if q.2.all (fun v => decide (q.1.1.1 ≤ v)) then q.2.mapIdx (bankCell q.1) else q.2

private theorem checkedBankMap_inSpace :
    ComputableInSpace checkedBankMap (encPair encBankPar (encList encNat)) (encList encNat)
      (fun q => (encPair encBankPar (encList encNat) q).length) := by
  have h := padding_inSpace.ite bankMap_inSpace (snd encBankPar (encList encNat))
  refine h.weaken ?_ |>.of_enc_eq fun _ => rfl
  refine .of_le_linear 8 8 fun q => ?_
  have hl := length_le_encPair_right encBankPar (encList encNat) q
  have hn := length_le_length_encList encNat q.2
  cases hc : q.2.all (fun v => decide (q.1.1.1 ≤ v)) with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
  | true =>
    have hw := padded_width_le_encoding q.1.1.1 q.2
      (fun v hv => of_decide_eq_true (List.all_eq_true.mp hc v hv))
    simp only [↓reduceIte]
    dsimp only [bankUpdateSpace]
    nlinarith

/-- Runtime modulus, register width, target and multiplier, followed by the bank. -/
abbrev BankArgs := (ℕ × ℕ × ℕ × ℕ) × List ℕ

/-- Binary encoding of one scalar bank-update request. -/
abbrev encBankArgs : BankArgs ↪ List Bool :=
  encPair (encPair encNat (encPair encNat (encPair encNat encNat))) (encList encNat)

/-- Runtime scalar parameters, a returned vector and the bank. -/
abbrev VectorBankArgs := (ℕ × ℕ × ℕ × ℕ) × List ℕ × List ℕ

/-- Binary encoding of one returned-vector bank-update request. -/
abbrev encVectorBankArgs : VectorBankArgs ↪ List Bool :=
  encPair (encPair encNat (encPair encNat (encPair encNat encNat)))
    (encPair (encList encNat) (encList encNat))

/-- Check the width charge before scaling. Invalid storage or a zero modulus is unchanged. -/
@[expose] def checkedScaleBank (q : BankArgs) : List ℕ :=
  if q.2.all (fun v => decide (q.1.1 ≤ v)) then
    if q.1.1 = 0 then q.2 else scaleBank q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2
  else q.2

/-- Check the width charge before adding a returned vector. -/
@[expose] def checkedAddBank (q : VectorBankArgs) : List ℕ :=
  if q.2.2.all (fun v => decide (q.1.1 ≤ v)) then
    if q.1.1 = 0 then q.2.2 else addBank q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2
  else q.2.2

/-- Check the width charge before subtracting a returned vector. -/
@[expose] def checkedSubBank (q : VectorBankArgs) : List ℕ :=
  if q.2.2.all (fun v => decide (q.1.1 ≤ v)) then
    if q.1.1 = 0 then q.2.2 else subBank q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2
  else q.2.2

private theorem mapIdx_identity (bank : List ℕ) : bank.mapIdx (fun _ v => v) = bank := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

private theorem mapIdx_bankCell (q : BankPar) (bank : List ℕ) :
    bank.mapIdx (bankCell q) = bank.mapIdx (fun k v =>
if q.1.1 = 0 then v else
    if k / q.1.2.1 = q.1.2.2.1 then
      q.1.1 + if q.2.2.1 then
        addMod q.1.1 v (if q.2.2.2 then
          negMod q.1.1 (mulMod q.1.1 q.1.2.2.2 (q.2.1.getD (k % q.1.2.1) 0))
        else mulMod q.1.1 q.1.2.2.2 (q.2.1.getD (k % q.1.2.1) 0))
      else mulMod q.1.1 q.1.2.2.2 v
    else v ) := rfl

/-- Scaling uses native space linear in the encoded arguments, including small zero cells. -/
theorem checkedScaleBank_inSpace :
    ComputableInSpace checkedScaleBank encBankArgs (encList encNat)
      (fun q => (encBankArgs q).length) := by
  have hpar := fst (encPair encNat (encPair encNat (encPair encNat encNat))) (encList encNat)
  have hbank := snd (encPair encNat (encPair encNat (encPair encNat encNat))) (encList encNat)
  have hprep := budget_prod
    (budget_prod hpar (budget_prod (budget_const (encB := encList encNat) [] (.refl _))
      (budget_const (encB := encPair encBool encBool) (false, false) (.refl _)))) hbank
  refine (budget_comp_linear checkedBankMap_inSpace hprep).of_enc_eq ?_
  intro q
  by_cases hpad : q.2.all (fun v => decide (q.1.1 ≤ v)) = true
  · by_cases hp : q.1.1 = 0
    · simp [checkedBankMap, mapIdx_bankCell, checkedScaleBank, hp, mapIdx_identity]
    · simp [checkedBankMap, mapIdx_bankCell, checkedScaleBank, hpad, hp, scaleBank]
  · simp [checkedBankMap, checkedScaleBank, hpad]

private theorem vectorBank_inSpace (subtract : Bool) :
    ComputableInSpace (fun q : VectorBankArgs =>
      checkedBankMap ((q.1, q.2.1, true, subtract), q.2.2))
      encVectorBankArgs (encList encNat) (fun q => (encVectorBankArgs q).length) := by
  have hpar := fst (encPair encNat (encPair encNat (encPair encNat encNat)))
    (encPair (encList encNat) (encList encNat))
  have hrest := snd (encPair encNat (encPair encNat (encPair encNat encNat)))
    (encPair (encList encNat) (encList encNat))
  have hprep := budget_prod
    (budget_prod hpar (budget_prod (fst' hrest)
      (budget_const (encB := encPair encBool encBool) (true, subtract) (.refl _))))
    (snd' hrest)
  exact budget_comp_linear checkedBankMap_inSpace hprep

/-- Adding a returned vector has a uniform native linear-space certificate. -/
theorem checkedAddBank_inSpace :
    ComputableInSpace checkedAddBank encVectorBankArgs (encList encNat)
      (fun q => (encVectorBankArgs q).length) := by
  refine (vectorBank_inSpace false).of_enc_eq ?_
  intro q
  by_cases hpad : q.2.2.all (fun v => decide (q.1.1 ≤ v)) = true
  · by_cases hp : q.1.1 = 0
    · simp [checkedBankMap, mapIdx_bankCell, checkedAddBank, hp, mapIdx_identity]
    · simp [checkedBankMap, mapIdx_bankCell, checkedAddBank, hpad, hp, addBank]
  · simp [checkedBankMap, checkedAddBank, hpad]

/-- Subtracting returned gate values has a uniform native linear-space certificate. -/
theorem checkedSubBank_inSpace :
    ComputableInSpace checkedSubBank encVectorBankArgs (encList encNat)
      (fun q => (encVectorBankArgs q).length) := by
  refine (vectorBank_inSpace true).of_enc_eq ?_
  intro q
  by_cases hpad : q.2.2.all (fun v => decide (q.1.1 ≤ v)) = true
  · by_cases hp : q.1.1 = 0
    · simp [checkedBankMap, mapIdx_bankCell, checkedSubBank, hp, mapIdx_identity]
    · simp [checkedBankMap, mapIdx_bankCell, checkedSubBank, hpad, hp, subBank]
  · simp [checkedBankMap, checkedSubBank, hpad]

/-- On the actual controller's valid bank the checked scale is its original scale. -/
theorem checkedScaleBank_eq (p d r t a : ℕ) (bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    checkedScaleBank ((p, r, t, a), bank) = scaleBank p r t a bank := by
  obtain ⟨hp, _, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  have hall : bank.all (fun v => decide (p ≤ v)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hpad
  simp [checkedScaleBank, hall, show p ≠ 0 by omega]

/-- On a valid bank the checked additive update is the actual controller update. -/
theorem checkedAddBank_eq (p d r t c : ℕ) (values bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    checkedAddBank ((p, r, t, c), values, bank) = addBank p r t c values bank := by
  obtain ⟨hp, _, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  have hall : bank.all (fun v => decide (p ≤ v)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hpad
  simp [checkedAddBank, hall, show p ≠ 0 by omega]

/-- On a valid bank the checked subtractive update is the actual controller update. -/
theorem checkedSubBank_eq (p d r t c : ℕ) (values bank : List ℕ)
    (hbank : validBank p d r bank = true) :
    checkedSubBank ((p, r, t, c), values, bank) = subBank p r t c values bank := by
  obtain ⟨hp, _, hpad⟩ := (validBank_eq_true p d r bank).mp hbank
  have hall : bank.all (fun v => decide (p ≤ v)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hpad
  simp [checkedSubBank, hall, show p ≠ 0 by omega]

/-- The per-cell padding check is itself uniformly native in the binary modulus and bank. -/
theorem bankPadding_inSpace :
    ComputableInSpace (fun q : ℕ × List ℕ => q.2.all (fun v => decide (q.1 ≤ v)))
      (encPair encNat (encList encNat)) encBool
      (fun q => (encPair encNat (encList encNat) q).length) := by
  have hp := fst encNat (encList encNat)
  have hbank := snd encNat (encList encNat)
  have hz := budget_const (encIn := encPair encNat (encList encNat))
    (encB := encNat) 0 (.refl _)
  have hpar := budget_prod hp (budget_prod hz (budget_prod hz hz))
  have hcontext := budget_prod hpar
    (budget_prod (budget_const (encB := encList encNat) [] (.refl _))
      (budget_const (encB := encPair encBool encBool) (false, false) (.refl _)))
  exact (budget_comp_linear padding_inSpace (budget_prod hcontext hbank)).of_enc_eq fun _ => rfl

end Cslib.TreeEval.Ary.Packed.RawController
