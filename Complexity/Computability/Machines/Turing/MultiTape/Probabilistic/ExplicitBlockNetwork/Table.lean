/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount

/-!
# The tables of an explicit block-counting network, on numbers

The tables of the explicit block-counting network of a schedule
(`Turing.MultiTapePTM.explicitBlockNetwork`) are values of the tensors of the block-counting
network (`Turing.MultiTapePTM.blockNetwork`) at letters read from the bits of a table index. This
module computes them from numbers, the form in which a polynomial-time construction produces
them.

* **Letters from numbers.** A letter is read as its number (`Turing.MultiTapePTM.letterEquiv`),
  and every natural number is decoded to a letter (`Turing.MultiTapePTM.decodeLetter`), inverting
  the numbering (`Turing.MultiTapePTM.decodeLetter_letterEquiv`). The control record of a number
  is computed on plain data by division and remainder (`Turing.MultiTapePTM.decodeControlData`),
  and so are the cells of block contents (`Turing.MultiTapePTM.contentsCellNum`) and the accepting
  weight (`Turing.MultiTapePTM.acceptNum`).
* **The window entering an interval.** The previous appearance of a block in windows is a search
  over the earlier intervals (`Turing.MultiTapePTM.lastBeforeNum_eq`), and its window entry is a
  digit-count difference (`Turing.MultiTapePTM.portOfNum`).
* **The tensors on numbers.** Given the numbers of the letters on all edges, the tensor of an
  interval is an interval count on plain data (`Turing.MultiTapePTM.localIntervalCount`) when the
  letters leaving it have the right kinds, and zero otherwise; the sinks are the accepting weight
  or `1` (`Turing.MultiTapePTM.blockNetwork_tensor_decodeLetter`).

## Main definitions

* `Turing.MultiTapePTM.decodeControlData`, `Turing.MultiTapePTM.decodeLetter`,
  `Turing.MultiTapePTM.contentsCellNum`, `Turing.MultiTapePTM.acceptNum`: decoding letters.
* `Turing.MultiTapePTM.lastBeforeNum`, `Turing.MultiTapePTM.portOfNum`: previous appearances and
  window entries on numbers.
* `Turing.MultiTapePTM.intervalEntryNum`, `Turing.MultiTapePTM.oldEntryNum`: the tensors of the
  block-counting network on numbers.

## Main results

* `Turing.MultiTapePTM.decodeControlData_controlEquiv`,
  `Turing.MultiTapePTM.decodeLetter_letterEquiv`: decoding inverts the numberings.
* `Turing.MultiTapePTM.card_intervalHolds`: the tensor of an interval is an interval count.
* `Turing.MultiTapePTM.blockNetwork_tensor_decodeLetter`: the tensors on numbers.
-/

public section

namespace Turing.MultiTapePTM

open Cslib.Circuits.Frontier MultiTapeNTM.ChoiceTable

variable {k q s : ℕ} {State : Type}

/-! ### Products of numberings -/

private theorem val_finProdFinEquiv_div {m n : ℕ} (x : Fin m × Fin n) :
    (finProdFinEquiv x : ℕ) / n = x.1 := by
  have := x.2.isLt
  rw [finProdFinEquiv_apply_val, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt x.2.isLt,
    zero_add]

private theorem val_finProdFinEquiv_mod {m n : ℕ} (x : Fin m × Fin n) :
    (finProdFinEquiv x : ℕ) % n = x.2 := by
  rw [finProdFinEquiv_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]

/-- Digit `r < b` in base `3` of a number is that of its remainder modulo `3 ^ b`. -/
private theorem mod_pow_div_pow_mod (x : ℕ) {r b : ℕ} (hr : r < b) :
    x % 3 ^ b / 3 ^ r % 3 = x / 3 ^ r % 3 := by
  obtain ⟨d, rfl⟩ : ∃ d, b = r + (d + 1) := ⟨b - r - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega))]

private theorem equivFin_symm_eq_accept_iff {t : ℕ} (ht : t < 3) :
    OutputTrack.equivFin.symm ⟨t, ht⟩ = .accept ↔ t = 1 := by
  interval_cases t <;> simp [OutputTrack.equivFin]

/-! ### Decoding letters -/

/-- The number of control records, which come first among the letters. -/
@[expose] def controlCount (k s b : ℕ) : ℕ := (s + 1) * (b ^ (k + 1) * 3)

/-- The number of letters. -/
@[expose] def letterCount (k s b : ℕ) : ℕ := controlCount k s b + 3 ^ b

section Decode

variable (e : State ≃ Fin s) (b : ℕ)

/-- The state numbered `i ≤ s`: none for `0`, and the state numbered `i - 1` by `e` otherwise. -/
@[expose] def stateOfFin (i : Fin (s + 1)) : Option State :=
  ((Equiv.optionCongr e).trans (finSuccEquiv s).symm).symm i

/-- **The control record of a number**, on plain data: the state from the quotient by
`b ^ (k + 1) * 3` (capped at `s`), the offsets as digits in base `b` and the output track from the
remainder. -/
@[expose] def decodeControlData (n : ℕ) : ControlData k State :=
  (stateOfFin e ⟨min s (n / (b ^ (k + 1) * 3)) % (s + 1), Nat.mod_lt _ (by omega)⟩,
    fun head => n % (b ^ (k + 1) * 3) / 3 / b ^ ((finSuccEquiv k).symm head : ℕ) % b,
    OutputTrack.equivFin.symm ⟨n % (b ^ (k + 1) * 3) % 3, Nat.mod_lt _ (by omega)⟩)

/-- **Decoding control records inverts their numbering.** -/
theorem decodeControlData_controlEquiv [NeZero b] (c : BlockControl k State b) :
    decodeControlData e b (controlEquiv e c) = controlData c := by
  obtain ⟨st, off, tr⟩ := c
  set x := controlEquiv e (st, off, tr)
  have hx : (x : ℕ) = (finProdFinEquiv (((Equiv.optionCongr e).trans (finSuccEquiv s).symm) st,
      finProdFinEquiv (finFunctionFinEquiv fun c => zmodEquiv b (off (finSuccEquiv k c)),
        OutputTrack.equivFin tr)) : ℕ) := rfl
  have hdiv : (x : ℕ) / (b ^ (k + 1) * 3) =
      ((Equiv.optionCongr e).trans (finSuccEquiv s).symm) st := by
    rw [hx, val_finProdFinEquiv_div]
  have hmod : (x : ℕ) % (b ^ (k + 1) * 3) = (finProdFinEquiv (finFunctionFinEquiv fun c =>
      zmodEquiv b (off (finSuccEquiv k c)), OutputTrack.equivFin tr) : ℕ) := by
    rw [hx, val_finProdFinEquiv_mod]
  have hst : stateOfFin e ⟨min s ((x : ℕ) / (b ^ (k + 1) * 3)) % (s + 1),
      Nat.mod_lt _ (by omega)⟩ = st := by
    have hlt := (((Equiv.optionCongr e).trans (finSuccEquiv s).symm) st).isLt
    have hfin : (⟨min s ((x : ℕ) / (b ^ (k + 1) * 3)) % (s + 1), Nat.mod_lt _ (by omega)⟩ :
        Fin (s + 1)) = ((Equiv.optionCongr e).trans (finSuccEquiv s).symm) st := by
      ext
      simp only
      rw [hdiv, Nat.min_eq_right (by omega), Nat.mod_eq_of_lt hlt]
    rw [hfin, stateOfFin, Equiv.symm_apply_apply]
  have htr : OutputTrack.equivFin.symm ⟨(x : ℕ) % (b ^ (k + 1) * 3) % 3,
      Nat.mod_lt _ (by omega)⟩ = tr := by
    have hfin : (⟨(x : ℕ) % (b ^ (k + 1) * 3) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) =
        OutputTrack.equivFin tr := by
      ext
      simp only
      rw [hmod, val_finProdFinEquiv_mod]
    rw [hfin, Equiv.symm_apply_apply]
  have hoff : ∀ head,
      (x : ℕ) % (b ^ (k + 1) * 3) / 3 / b ^ ((finSuccEquiv k).symm head : ℕ) % b =
        (off head).val := by
    intro head
    rw [hmod, val_finProdFinEquiv_div, ← finFunctionFinEquiv_symm_apply_val,
      Equiv.symm_apply_apply, val_zmodEquiv, Equiv.apply_symm_apply]
  simp only [decodeControlData, controlData, hst, htr, hoff]

/-- The control record entering an interval from a letter number: the decoded record of a control
letter, and the default record of block contents. -/
@[expose] def controlDataOfNum (n : ℕ) : ControlData k State :=
  if n < controlCount k s b then decodeControlData e b n else (none, fun _ => 0, .empty)

/-- The cell `r` of the block contents numbered `n`, blank for a control record. -/
@[expose] def contentsCellNum (k s b n r : ℕ) : Option Bool :=
  if n < controlCount k s b then none
  else cellEquiv.symm ⟨(n - controlCount k s b) / 3 ^ r % 3, Nat.mod_lt _ (by omega)⟩

/-- The accepting weight of the letter numbered `n`: one for a control record with output track
`accept`. -/
@[expose] def acceptNum (k s b n : ℕ) : ℕ :=
  if n < controlCount k s b ∧ n % (b ^ (k + 1) * 3) % 3 = 1 then 1 else 0

variable [NeZero b]

/-- **The letter of a number**: the control record of that number for a number below
`controlCount`, and otherwise the block contents of the remainder of `n - controlCount` modulo
`3 ^ b`. Below `letterCount` this inverts `Turing.MultiTapePTM.letterEquiv`. -/
@[expose] def decodeLetter (n : ℕ) : BlockLetter k State b :=
  if h : n < controlCount k s b then .inl ((controlEquiv e).symm ⟨n, h⟩)
  else .inr ((contentsEquiv b).symm
    ⟨(n - controlCount k s b) % 3 ^ b, Nat.mod_lt _ (by positivity)⟩)

/-- **Decoding letters inverts their numbering.** -/
theorem decodeLetter_letterEquiv (l : BlockLetter k State b) :
    decodeLetter e b (letterEquiv e l) = l := by
  rcases l with c | w
  · have hval : (letterEquiv e (.inl c) : ℕ) = controlEquiv e c := by
      simp [letterEquiv]
    have hlt : (letterEquiv e (.inl c) : ℕ) < controlCount k s b := by
      rw [hval]
      exact (controlEquiv e c).isLt
    rw [decodeLetter, dite_eq_left hlt]
    congr 1
    rw [Equiv.symm_apply_eq]
    exact Fin.ext hval.symm
  · have hval : (letterEquiv e (.inr w : BlockLetter k State b) : ℕ) =
        controlCount k s b + contentsEquiv b w := by
      simp [letterEquiv, controlCount]
    rw [decodeLetter, dite_eq_right (by omega)]
    congr 1
    rw [Equiv.symm_apply_eq]
    ext
    simp only [hval, Nat.add_sub_cancel_left]
    exact Nat.mod_eq_of_lt (contentsEquiv b w).isLt

/-- Below `letterCount`, the letter of a number is the numbered letter. -/
theorem decodeLetter_of_lt {n : ℕ} (hn : n < letterCount k s b) :
    decodeLetter e b n = (letterEquiv e).symm ⟨n, hn⟩ := by
  conv_lhs => rw [show n = (letterEquiv e ((letterEquiv e).symm ⟨n, hn⟩) : ℕ) by simp]
  exact decodeLetter_letterEquiv e b _

/-- The control record of a decoded letter. -/
theorem controlData_control_decodeLetter (n : ℕ) :
    controlData (decodeLetter (k := k) e b n).control = controlDataOfNum e b n := by
  unfold decodeLetter controlDataOfNum
  split_ifs with h
  · simp only [BlockLetter.control]
    rw [← decodeControlData_controlEquiv e b, Equiv.apply_symm_apply]
  · simp only [BlockLetter.control, controlData, Pi.zero_apply, ZMod.val_zero]

/-- The cells of a decoded letter. -/
theorem contents_decodeLetter (n : ℕ) (r : ZMod b) :
    (decodeLetter (k := k) e b n).contents r = contentsCellNum k s b n r.val := by
  unfold decodeLetter contentsCellNum
  split_ifs with h
  · rfl
  · simp only [BlockLetter.contents, contentsEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm,
      Equiv.arrowCongr_apply, Function.comp_apply, Equiv.symm_symm]
    congr 1
    ext
    rw [finFunctionFinEquiv_symm_apply_val]
    simp only [val_zmodEquiv]
    exact mod_pow_div_pow_mod _ (ZMod.val_lt r)

/-- The accepting weight of a decoded letter. -/
theorem acceptWeight_decodeLetter (n : ℕ) :
    acceptWeight (decodeLetter (k := k) e b n) = acceptNum k s b n := by
  unfold decodeLetter acceptNum
  by_cases h : n < controlCount k s b
  · have hc := decodeControlData_controlEquiv e b ((controlEquiv e).symm ⟨n, h⟩)
    rw [Equiv.apply_symm_apply] at hc
    have htr := congrArg (fun c => c.2.2) hc
    simp only [decodeControlData, controlData] at htr
    simp only [h, ↓reduceDIte, acceptWeight, ← htr, equivFin_symm_eq_accept_iff, true_and]
  · simp only [h, ↓reduceDIte, acceptWeight, false_and, ↓reduceIte]

end Decode

/-! ### The window entering an interval, on numbers -/

/-- The last interval before `i` whose window contains the block `δ` of interval `i`'s window,
for the head with digit offset `c`, found by searching the earlier intervals from the latest. -/
@[expose] def lastBeforeNum (k σ c i δ : ℕ) : Option ℕ :=
  ((List.range i).find? fun j => inWindowNum k σ c i δ (i - 1 - j)).map fun j => i - 1 - j

/-- **Previous appearances on numbers.** -/
theorem lastBeforeNum_eq (σ : ℕ) (i : Fin q) (h : Fin k) (δ : Fin 3) :
    lastBeforeNum k σ (h + 1) i δ =
      (lastBefore (InWindow (scheduleOfNat k q σ) h
        (portBlock (scheduleOfNat k q σ) i h δ)) i).map Fin.val := by
  cases hl : lastBefore (InWindow (scheduleOfNat k q σ) h
      (portBlock (scheduleOfNat k q σ) i h δ)) i with
  | none =>
    rw [lastBefore_eq_none_iff] at hl
    simp only [Option.map_none, lastBeforeNum, Option.map_eq_none_iff, List.find?_eq_none,
      List.mem_range]
    intro j hj hw
    exact hl ⟨i - 1 - j, by omega⟩ (Fin.lt_def.mpr (by simp only; omega))
      ((inWindowNum_iff σ i ⟨i - 1 - j, by omega⟩ h δ).mp hw)
  | some i' =>
    obtain ⟨hlt, hw, hmax⟩ := lastBefore_eq_some_iff.mp hl
    have hlt' : (i' : ℕ) < i := hlt
    have hfind : (List.range i).find? (fun j => inWindowNum k σ (h + 1) i δ (i - 1 - j)) =
        some ((i : ℕ) - 1 - i') := by
      rw [List.find?_range_eq_some]
      refine ⟨?_, List.mem_range.mpr (by omega), fun j hj => ?_⟩
      · rw [show (i : ℕ) - 1 - (i - 1 - i') = i' by omega]
        exact (inWindowNum_iff σ i i' h δ).mpr hw
      · rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
          inWindowNum_iff σ i ⟨i - 1 - j, by omega⟩ h δ]
        exact hmax ⟨i - 1 - j, by omega⟩ (Fin.lt_def.mpr (by simp only; omega))
          (Fin.lt_def.mpr (by simp only; omega))
    simp only [lastBeforeNum, hfind, Option.map_some, Option.some.injEq]
    omega

/-- The window entry, in the window of interval `i'`, of the block `δ` of interval `i`'s window,
for the head with digit offset `c`: `b(i) + δ - b(i') mod 3` from the digit counts. -/
@[expose] def portOfNum (k σ c i i' δ : ℕ) : ℕ :=
  (digitCount k σ c 2 i + digitCount k σ c 0 i' + δ -
    (digitCount k σ c 0 i + digitCount k σ c 2 i')) % 3

/-- **Window entries on numbers.** -/
theorem val_portOf (σ : ℕ) (i i' : Fin q) (h : Fin k) (δ : Fin 3) :
    (portOf (scheduleOfNat k q σ) i' h (portBlock (scheduleOfNat k q σ) i h δ) : ℕ) =
      portOfNum k σ (h + 1) i i' δ := by
  have hc : (((finSuccEquiv k).symm (some h) : Fin (k + 1)) : ℕ) = h + 1 := by simp
  have hb := scheduleBlock_scheduleOfNat (k := k) σ i.isLt.le (some h)
  have hb' := scheduleBlock_scheduleOfNat (k := k) σ i'.isLt.le (some h)
  rw [hc] at hb hb'
  simp only [portOf, portBlock, hb, hb', portOfNum]
  congr 1
  omega

/-! ### The tensor of an interval -/

section Interval

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ) (σ : Schedule k q)

open scoped Classical in
/-- **The tensor of an interval is an interval count** when the letters leaving it are a control
record and block contents. -/
theorem card_intervalHolds (i : Fin q) {x : BlockEdge k q → BlockLetter k State b}
    {cOut : BlockControl k State b} {wOut : Fin k → Fin 3 → ZMod b → Option Bool}
    (hc : x (.inl i) = .inl cOut) (hw : ∀ h d, x (.inr (i, h, d)) = .inr (wOut h d)) :
    (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card =
      machine.intervalCount b input (scheduleBlock σ i) (σ i) (machine.inControl b i x)
        (inWindow σ i x) cOut wOut := by
  unfold intervalCount
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, IntervalHolds, hc, hw, Sum.inl.injEq,
    Sum.inr.injEq]
  constructor
  · rintro ⟨c', w', hstep, rfl, hw'⟩
    obtain rfl : w' = wOut := funext fun h => funext fun d => (hw' h d).symm
    exact hstep
  · exact fun hstep => ⟨cOut, wOut, hstep, rfl, fun _ _ => rfl⟩

open scoped Classical in
/-- The tensor of an interval vanishes when a letter leaving it has the wrong kind. -/
theorem card_intervalHolds_eq_zero (i : Fin q) {x : BlockEdge k q → BlockLetter k State b}
    (hx : ¬ ((∃ cOut, x (.inl i) = .inl cOut) ∧ ∀ h d, ∃ w, x (.inr (i, h, d)) = .inr w)) :
    (Finset.univ.filter fun u => machine.IntervalHolds input b σ i x u).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro u - ⟨cOut, wOut, -, hc, hw⟩
  exact hx ⟨⟨cOut, hc⟩, fun h d => ⟨_, hw h d⟩⟩

end Interval

/-! ### The tensors on numbers -/

section Tensors

variable (e : State ≃ Fin s) (b : ℕ)

/-- The block indices at the start of interval `i` of the schedule of `σ`, as digit counts. -/
@[expose] def blockIndexNum (k σ i : ℕ) : Option (Fin k) → ℤ := fun head =>
  (digitCount k σ ((finSuccEquiv k).symm head) 2 i : ℤ) -
    digitCount k σ ((finSuccEquiv k).symm head) 0 i

/-- The movements of the blocks in interval `i` of the schedule of `σ`. -/
@[expose] def blockMoveNum (k σ i : ℕ) : Option (Fin k) → SignType := fun head =>
  signEquiv.symm ⟨σ / 3 ^ (((finSuccEquiv k).symm head : ℕ) + (k + 1) * i) % 3,
    Nat.mod_lt _ (by norm_num)⟩

/-- The control record entering interval `i`, from the letter numbers `L` of the edges. -/
@[expose] def inControlNum (initial : State) (L : ℕ → ℕ) (i : ℕ) : ControlData k State :=
  if i = 0 then (some initial, fun _ => 0, .empty) else controlDataOfNum e b (L (i - 1))

/-- The cells of the window of work tape `h` entering interval `i`, from the letter numbers `L`
of the edges of a schedule number `σ` with `q` intervals. -/
@[expose] def inCellsNum (k q s b σ : ℕ) (L : ℕ → ℕ) (i h : ℕ) : List (Option Bool) :=
  (List.range (3 * b)).map fun c =>
    (lastBeforeNum k σ (h + 1) i (c / b)).elim none fun i' =>
      contentsCellNum k s b (L (q + (portOfNum k σ (h + 1) i i' (c / b) + 3 * h + k * 3 * i')))
        (c % b)

/-- The cells of the window of work tape `h` leaving interval `i`, from the letter numbers `L`
of the edges. -/
@[expose] def outCellsNum (k q s b : ℕ) (L : ℕ → ℕ) (i h : ℕ) : List (Option Bool) :=
  (List.range (3 * b)).map fun c =>
    contentsCellNum k s b (L (q + (c / b + 3 * h + k * 3 * i))) (c % b)

variable [DecidableEq State] (machine : MultiTapePTM k Bool State) (input : List Bool)

/-- **The tensor of interval `i` on numbers**, from the letter numbers `L` of the edges: the
interval count on plain data when the control edge leaving `i` carries a control record and its
block edges carry block contents, and zero otherwise. -/
@[expose] def intervalEntryNum (q σ : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if L i < controlCount k s b ∧
      ∀ h : Fin k, ∀ δ : Fin 3, ¬ L (q + (δ + 3 * h + k * 3 * i)) < controlCount k s b then
    machine.localIntervalCount b input (blockIndexNum k σ i) (blockMoveNum k σ i)
      (inControlNum e b machine.initial L i) (fun h => inCellsNum k q s b σ L i h)
      (decodeControlData e b (L i)) (fun h => outCellsNum k q s b L i h)
  else 0

/-- **The tensor of an old vertex on numbers**: an interval (`v < q`), or the sink of the edge
numbered `v - q`, which accepts the last control record and is `1` otherwise. -/
@[expose] def oldEntryNum (q σ : ℕ) (L : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v < q then intervalEntryNum e b machine input q σ L v
  else if v - q + 1 = q then acceptNum k s b (L (v - q)) else 1

end Tensors

/-! ### The tensors of the block-counting network on numbers -/

section TensorEq

variable (e : State ≃ Fin s) (b : ℕ) [NeZero b]

/-- A decoded letter is a control record exactly below `controlCount`. -/
theorem exists_decodeLetter_eq_inl_iff (n : ℕ) :
    (∃ c, decodeLetter (k := k) e b n = .inl c) ↔ n < controlCount k s b := by
  unfold decodeLetter
  split_ifs with h
  · exact iff_of_true ⟨_, rfl⟩ h
  · exact iff_of_false (by rintro ⟨c, hc⟩; cases hc) h

/-- A decoded letter is block contents exactly from `controlCount` on. -/
theorem exists_decodeLetter_eq_inr_iff (n : ℕ) :
    (∃ w, decodeLetter (k := k) e b n = .inr w) ↔ ¬ n < controlCount k s b := by
  unfold decodeLetter
  split_ifs with h
  · exact iff_of_false (by rintro ⟨c, hc⟩; cases hc) (not_not.mpr h)
  · exact iff_of_true ⟨_, rfl⟩ h

variable [DecidableEq State] (machine : MultiTapePTM k Bool State) (input : List Bool)

/-- **The tensors of the block-counting network on numbers.** At the letters decoded from numbers
`L` of the edges (`Turing.MultiTapePTM.decodeLetter`), the tensor of an old vertex of the explicit
network is `Turing.MultiTapePTM.oldEntryNum` at its number. -/
theorem blockNetwork_tensor_decodeLetter (σ : ℕ) (u : Fin q ⊕ BlockEdge k q) (L : ℕ → ℕ) :
    (machine.blockNetwork input b (scheduleOfNat k q σ)).tensor u
        (fun e' => decodeLetter e b (L (blockEdgeEquiv k q e'))) =
      oldEntryNum e b machine input q σ L
        (explicitVertexEquiv k q (letterBits k s b) (.inl u)) := by
  set x : BlockEdge k q → BlockLetter k State b :=
    fun e' => decodeLetter e b (L (blockEdgeEquiv k q e'))
  rcases u with i | i | ⟨i, h₀, d₀⟩
  · rw [val_explicitVertexEquiv_interval, oldEntryNum, ite_eq_left i.isLt, intervalEntryNum,
      blockNetwork_tensor_interval]
    have hxl : x (.inl i) = decodeLetter e b (L i) := by
      simp only [x, val_blockEdgeEquiv_inl]
    have hxr : ∀ (i' : Fin q) h d, x (.inr (i', h, d)) =
        decodeLetter e b (L (q + (d + 3 * h + k * 3 * i'))) := by
      intro i' h d
      simp only [x, val_blockEdgeEquiv_inr]
    split_ifs with hcond
    · obtain ⟨hctl, hblk⟩ := hcond
      have hc : x (.inl i) = .inl (x (.inl i)).control := by
        obtain ⟨c, hc⟩ := (exists_decodeLetter_eq_inl_iff e b _).mpr hctl
        rw [hxl, hc]
        rfl
      have hw : ∀ h d, x (.inr (i, h, d)) = .inr (x (.inr (i, h, d))).contents := by
        intro h d
        obtain ⟨w, hw⟩ := (exists_decodeLetter_eq_inr_iff e b _).mpr (hblk h d)
        rw [hxr, hw]
        rfl
      rw [card_intervalHolds machine input b _ i hc hw, ← localIntervalCount_eq_intervalCount]
      congr 1
      · funext head
        exact scheduleBlock_scheduleOfNat σ i.isLt.le head
      · unfold inControl inControlNum
        split_ifs with h0
        · simp only [controlData, Pi.zero_apply, ZMod.val_zero]
        · have : x (.inl ⟨i - 1, by omega⟩) = decodeLetter e b (L (i - 1)) := by
            simp only [x, val_blockEdgeEquiv_inl]
          rw [this, controlData_control_decodeLetter]
      · funext h
        unfold windowCells inCellsNum
        refine List.map_congr_left fun c hc => ?_
        have hc3 : c / b < 3 := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_neZero b)]
          simpa [Nat.mul_comm] using List.mem_range.mp hc
        rw [dite_eq_left hc3, inWindow, lastBeforeNum_eq σ i h ⟨c / b, hc3⟩]
        cases lastBefore (InWindow (scheduleOfNat k q σ) h
            (portBlock (scheduleOfNat k q σ) i h ⟨c / b, hc3⟩)) i with
        | none => rfl
        | some i' =>
          simp only [Option.elim_some, Option.map_some]
          rw [hxr, contents_decodeLetter, ZMod.val_natCast, val_portOf σ i i' h ⟨c / b, hc3⟩]
      · rw [hxl, controlData_control_decodeLetter, controlDataOfNum, ite_eq_left hctl]
      · funext h
        unfold windowCells outCellsNum
        refine List.map_congr_left fun c hc => ?_
        have hc3 : c / b < 3 := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_neZero b)]
          simpa [Nat.mul_comm] using List.mem_range.mp hc
        rw [dite_eq_left hc3]
        simp only
        rw [hxr, contents_decodeLetter, ZMod.val_natCast]
    · refine card_intervalHolds_eq_zero machine input b _ i fun ⟨⟨c, hc⟩, hw⟩ => hcond ⟨?_, ?_⟩
      · rw [hxl] at hc
        exact (exists_decodeLetter_eq_inl_iff e b _).mp ⟨c, hc⟩
      · intro h d
        obtain ⟨w, hw⟩ := hw h d
        rw [hxr] at hw
        exact (exists_decodeLetter_eq_inr_iff e b _).mp ⟨w, hw⟩
  · rw [val_explicitVertexEquiv_sink, val_blockEdgeEquiv_inl, oldEntryNum,
      ite_eq_right (by omega), blockNetwork_tensor_controlSink, Nat.add_sub_cancel_left]
    have hxl : x (.inl i) = decodeLetter e b (L i) := by
      simp only [x, val_blockEdgeEquiv_inl]
    rw [hxl, acceptWeight_decodeLetter]
  · rw [val_explicitVertexEquiv_sink, val_blockEdgeEquiv_inr, oldEntryNum,
      ite_eq_right (by omega), ite_eq_right (by omega), blockNetwork_tensor_blockSink]

end TensorEq

/-! ### Reading letters from table indices -/

section Read

variable (e : State ≃ Fin s) (b : ℕ) [NeZero b]

/-- Bits are the code of a letter exactly when they write its number. -/
theorem letterCode_eq_iff (l : BlockLetter k State b) (bits : Fin (letterBits k s b) → Bool) :
    letterCode e l = bits ↔ (letterEquiv e l : ℕ) = Cslib.BitString.lsbValue (List.ofFn bits) := by
  have hlt : (letterEquiv e l : ℕ) < 2 ^ letterBits k s b :=
    (letterEquiv e l).isLt.trans_le card_letter_le_two_pow
  constructor
  · rintro rfl
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Cslib.BitString.testBit_lsbValue]
    by_cases hi : i < letterBits k s b
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      rfl
    · rw [List.getD_eq_default _ _ (by simpa using hi),
        Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right two_pos (not_lt.mp hi)))]
  · intro h
    funext r
    simp only [letterCode, h, Cslib.BitString.testBit_lsbValue]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact r.isLt), List.getElem_ofFn]

/-- **Reading a letter code**: bits are the code of a letter exactly when the number they write is
below `letterCount`. -/
theorem mem_range_letterCode_iff (bits : Fin (letterBits k s b) → Bool) :
    bits ∈ Set.range (letterCode (k := k) e) ↔
      Cslib.BitString.lsbValue (List.ofFn bits) < letterCount k s b := by
  constructor
  · rintro ⟨l, hl⟩
    rw [← (letterCode_eq_iff e b l bits).mp hl]
    exact (letterEquiv e l).isLt
  · intro h
    exact ⟨(letterEquiv e).symm ⟨_, h⟩, (letterCode_eq_iff e b _ bits).mpr (by simp)⟩

/-- The letter read from the code `bits` is the decoded letter of their number. -/
theorem invFun_letterCode {bits : Fin (letterBits k s b) → Bool}
    (h : Cslib.BitString.lsbValue (List.ofFn bits) < letterCount k s b) :
    Function.invFun (letterCode (k := k) e) bits =
      decodeLetter e b (Cslib.BitString.lsbValue (List.ofFn bits)) := by
  have hmem := (mem_range_letterCode_iff e b bits).mpr h
  have hinv := Function.invFun_eq hmem
  rw [letterCode_eq_iff] at hinv
  rw [← hinv, decodeLetter_letterEquiv]

end Read

/-! ### The tables on numbers -/

section Tables

/-- The letter number read from the table index `j` at the `m` port numbers `base, …,
base + m - 1` of the port list `P`: its bit `r` is the bit of `j` at the position of port
`base + r` in `P`. -/
@[expose] def readNum (m : ℕ) (P : List ℕ) (j base : ℕ) : ℕ :=
  Cslib.BitString.lsbValue ((List.range m).map fun r => j.testBit (P.idxOf (base + r)))

/-- The first number of the explicit edges of the block edge numbered `n` at the old vertex
numbered `v`: its source halves when `v` is the interval it leaves, and its target halves
otherwise. -/
@[expose] def halfBase (k q m v n : ℕ) : ℕ :=
  if blockSrcNum k q n = v then m * n else q * (3 * k + 1) * m + m * n

/-- The letter numbers of the block edges read at the old vertex numbered `v` from the table
index `j` and the ports `P`. -/
@[expose] def lettersAt (k q m : ℕ) (P : List ℕ) (j v : ℕ) (n : ℕ) : ℕ :=
  readNum m P j (halfBase k q m v n)

/-- Whether every block edge at the old vertex numbered `v` carries a letter number, read from
the table index `j` and the ports `P`, below `letterCount`. -/
@[expose] def validNum (k q s b σ : ℕ) (P : List ℕ) (j v : ℕ) : Bool :=
  (List.range (q * (3 * k + 1))).all fun n =>
    !decide (blockSrcNum k q n = v ∨ edgeTargetNum k q σ n = v) ||
      decide (lettersAt k q (letterBits k s b) P j v n < letterCount k s b)

variable (e : State ≃ Fin s) (b : ℕ) [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (input : List Bool)

/-- **The table entry on numbers** of the vertex numbered `v` with ports `P` at the table index
`j`: for an old vertex, its tensor at the letters read from `j` when they are all valid, and zero
otherwise; for the subdivision vertex of a copy, equality of the bits on its two halves. -/
@[expose] def tableEntryNum (q σ v : ℕ) (P : List ℕ) (j : ℕ) : ℕ :=
  if v < q * (3 * k + 2) then
    if validNum k q s b σ P j v then
      oldEntryNum e b machine input q σ (lettersAt k q (letterBits k s b) P j v) v
    else 0
  else if j.testBit (P.idxOf (v - q * (3 * k + 2))) =
      j.testBit (P.idxOf (q * (3 * k + 1) * letterBits k s b + (v - q * (3 * k + 2)))) then 1
    else 0

/-- **The table on numbers** of the vertex numbered `v`: its entries at all indices below
`2 ^ (number of ports)`. -/
@[expose] def explicitTableNum (q σ v : ℕ) : List ℕ :=
  (List.range (2 ^ (explicitPortsNum k q (letterBits k s b) σ v).length)).map
    (tableEntryNum e b machine input q σ v (explicitPortsNum k q (letterBits k s b) σ v))

/-- **The vertices of the explicit network on numbers**: the ports and the table of every vertex
number. -/
@[expose] def explicitVerticesNum (q σ : ℕ) : List (List ℕ × List ℕ) :=
  (List.range (q * (3 * k + 2) + q * (3 * k + 1) * letterBits k s b)).map fun v =>
    (explicitPortsNum k q (letterBits k s b) σ v, explicitTableNum e b machine input q σ v)

private theorem idxOf_map_val {n : ℕ} (l : List (Fin n)) (a : Fin n) :
    (l.map Fin.val).idxOf a.val = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.idxOf_cons, ih, beq_iff_eq, Fin.val_inj]

private theorem ofFn_eq_map_range {m : ℕ} (f : ℕ → Bool) :
    List.ofFn (fun r : Fin m => f r) = (List.range m).map f := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

variable [NeZero b]

/-- **The tables of the explicit network on numbers**: the table of every vertex of the
binarized, subdivided network, with the edges numbered by `explicitEdgeEquiv`, is
`explicitTableNum` at the number of the vertex. -/
theorem explicitTable_eq_explicitTableNum (σ : ℕ)
    (w : (Fin q ⊕ BlockEdge k q) ⊕ BlockEdge k q × Fin (letterBits k s b)) :
    ((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize
        (letterCode e)).subdivide.explicitTable (explicitEdgeEquiv k q (letterBits k s b)) w =
      explicitTableNum e b machine input q σ (explicitVertexEquiv k q (letterBits k s b) w) := by
  set BN := machine.blockNetwork input b (scheduleOfNat k q σ)
  set ee := explicitEdgeEquiv k q (letterBits k s b)
  set ev := explicitVertexEquiv k q (letterBits k s b)
  set P := explicitPortsNum k q (letterBits k s b) σ (ev w)
  have hP : ((BN.binarize (letterCode e)).subdivide.explicitPorts ee w).map Fin.val = P :=
    map_val_explicitPorts machine input b (letterCode e) σ w
  have hidx : ∀ p, ((BN.binarize (letterCode e)).subdivide.explicitPorts ee w).idxOf (ee p) =
      P.idxOf (ee p : ℕ) := fun p => by rw [← hP, idxOf_map_val]
  unfold TensorNetwork.explicitTable explicitTableNum
  rw [show ((BN.binarize (letterCode e)).subdivide.explicitPorts ee w).length = P.length by
    rw [← hP, List.length_map]]
  refine List.map_congr_left fun j _ => ?_
  simp only [hidx]
  rcases w with u | ⟨e₀, r⟩
  · -- An old vertex.
    have hv : (ev (.inl u) : ℕ) < q * (3 * k + 2) := explicitVertexEquiv_inl k q _ u
    rw [tableEntryNum, ite_eq_left hv, TensorNetwork.subdivide_tensor_inl]
    simp only [TensorNetwork.binarize]
    -- The bits on the copies of an edge, and their number.
    have hsrc : ∀ e' : BlockEdge k q,
        BN.src e' = u ↔ blockSrcNum k q (blockEdgeEquiv k q e') = ev (.inl u) := by
      intro e'
      rw [blockSrcNum_blockEdgeEquiv (letterBits k s b) e', blockNetwork_src, Fin.val_inj,
        Equiv.apply_eq_iff_eq]
      simp only [Sum.inl.injEq]
    have htgt : ∀ e' : BlockEdge k q,
        BN.tgt e' = u ↔ edgeTargetNum k q σ (blockEdgeEquiv k q e') = ev (.inl u) := by
      intro e'
      rw [edgeTargetNum_blockEdgeEquiv σ (letterBits k s b) e', blockNetwork_tgt, Fin.val_inj,
        Equiv.apply_eq_iff_eq]
      simp only [Sum.inl.injEq]
    have hbits : ∀ e' : BlockEdge k q,
        Cslib.BitString.lsbValue (List.ofFn (TensorNetwork.bitsOn (fun p =>
          if BN.src p.1 = u then j.testBit (P.idxOf (ee (.inl p) : ℕ))
          else j.testBit (P.idxOf (ee (.inr p) : ℕ))) e')) =
          lettersAt k q (letterBits k s b) P j (ev (.inl u)) (blockEdgeEquiv k q e') := by
      intro e'
      simp only [lettersAt, readNum, halfBase, ← hsrc e']
      rw [← ofFn_eq_map_range]
      refine congrArg (fun l => Cslib.BitString.lsbValue (List.ofFn l)) (funext fun r => ?_)
      rw [TensorNetwork.bitsOn_apply]
      split_ifs
      · rw [val_explicitEdgeEquiv_inl, Nat.add_comm]
      · rw [val_explicitEdgeEquiv_inr, Nat.add_left_comm, Nat.add_comm (r : ℕ)]
    have hinc : ∀ e' : BlockEdge k q, (BN.src e' = u ∨ BN.tgt e' = u) ↔
        (blockSrcNum k q (blockEdgeEquiv k q e') = ev (.inl u) ∨
          edgeTargetNum k q σ (blockEdgeEquiv k q e') = ev (.inl u)) := fun e' => by
      rw [hsrc, htgt]
    have hall : validNum k q s b σ P j (ev (.inl u)) = true ↔ ∀ e' : BlockEdge k q,
        (BN.src e' = u ∨ BN.tgt e' = u) →
          lettersAt k q (letterBits k s b) P j (ev (.inl u)) (blockEdgeEquiv k q e') <
            letterCount k s b := by
      rw [validNum, List.all_eq_true]
      simp only [List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      constructor
      · intro h e' he'
        exact (h _ (blockEdgeEquiv k q e').isLt).resolve_left (not_not.mpr ((hinc e').mp he'))
      · intro h n hn
        obtain ⟨e', rfl⟩ : ∃ e', (blockEdgeEquiv k q e' : ℕ) = n :=
          ⟨(blockEdgeEquiv k q).symm ⟨n, hn⟩, by simp⟩
        by_cases he' : BN.src e' = u ∨ BN.tgt e' = u
        · exact Or.inr (h e' he')
        · exact Or.inl (fun h' => he' ((hinc e').mpr h'))
    split_ifs with h1 h2 h2
    · rw [← blockNetwork_tensor_decodeLetter]
      refine BN.tensor_congr _ _ _ fun e' he' => ?_
      have hlt := (mem_range_letterCode_iff e b _).mp (h1 e' he')
      rw [invFun_letterCode e b hlt]
      exact congrArg (decodeLetter e b) (hbits e')
    · exact absurd (hall.mpr fun e' he' =>
        (hbits e').symm.trans_lt ((mem_range_letterCode_iff e b _).mp (h1 e' he'))) h2
    · exact absurd (fun e' he' => (mem_range_letterCode_iff e b _).mpr
        ((hbits e').trans_lt (hall.mp h2 e' he'))) h1
    · rfl
  · -- A subdivision vertex.
    have hv : q * (3 * k + 2) ≤ (ev (.inr (e₀, r)) : ℕ) := le_explicitVertexEquiv_inr k q _ _
    have hc : (ev (.inr (e₀, r)) : ℕ) - q * (3 * k + 2) =
        r + letterBits k s b * blockEdgeEquiv k q e₀ := by
      rw [val_explicitVertexEquiv_inr]
      omega
    rw [tableEntryNum, ite_eq_right (by omega), TensorNetwork.subdivide_tensor_inr, hc,
      val_explicitEdgeEquiv_inl, val_explicitEdgeEquiv_inr]

/-- **The explicit block-counting network on numbers**: `2 q (3 k + 1) m` edges and the vertices
`explicitVerticesNum`. -/
@[expose] def explicitNetworkNum (q σ : ℕ) : ExplicitTensorNetwork ℕ where
  numEdges := 2 * (q * (3 * k + 1) * letterBits k s b)
  vertices := explicitVerticesNum e b machine input q σ

/-- **The explicit block-counting network is computed on numbers**: for the schedule of `σ`,
`explicitBlockNetwork` is `explicitNetworkNum`. -/
theorem explicitBlockNetwork_eq_explicitNetworkNum (σ : ℕ) :
    machine.explicitBlockNetwork input b (scheduleOfNat k q σ) e =
      explicitNetworkNum e b machine input q σ := by
  have hv : (machine.explicitBlockNetwork input b (scheduleOfNat k q σ) e).vertices =
      explicitVerticesNum e b machine input q σ := by
    rw [explicitBlockNetwork, TensorNetwork.toExplicit, explicitVerticesNum,
      ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply]
    rw [map_val_explicitPorts, explicitTable_eq_explicitTableNum, Equiv.apply_symm_apply]
  cases h : machine.explicitBlockNetwork input b (scheduleOfNat k q σ) e with
  | mk n vs =>
    rw [h] at hv
    have hn := numEdges_explicitBlockNetwork machine input b (scheduleOfNat k q σ) e
    rw [h] at hn
    simp only at hv hn
    rw [explicitNetworkNum, hv, hn]

end Tables

/-! ### Port counts -/

section PortCounts

/-- Every explicit edge starts at an old vertex. -/
theorem explicitSrcNum_lt {m σ j : ℕ} (hj : j < 2 * (q * (3 * k + 1) * m)) :
    explicitSrcNum k q m σ j < q * (3 * k + 2) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hj
    · exact hm
  unfold explicitSrcNum
  split_ifs with hlt
  · have hn : j / m < q * (3 * k + 1) := (Nat.div_lt_iff_lt_mul hm).mpr hlt
    unfold blockSrcNum
    split_ifs with hq
    · nlinarith
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · omega
      · have : (j / m - q) / (k * 3) < q := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          have : q * (3 * k + 1) = q + q * (k * 3) := by ring
          omega
        nlinarith
  · have hn : (j - q * (3 * k + 1) * m) / m < q * (3 * k + 1) :=
      (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    set n := (j - q * (3 * k + 1) * m) / m
    unfold edgeTargetNum
    split_ifs with h1 h2
    · nlinarith
    · nlinarith
    · cases hf : firstAfterNum k q σ ((n - q) % (k * 3) / 3 + 1) ((n - q) / (k * 3)) ((n - q) % 3)
        with
      | none => simp only [Option.getD_none]; nlinarith
      | some i' =>
        have hmem := List.mem_of_find?_eq_some hf
        rw [List.mem_range] at hmem
        simp only [Option.getD_some]
        nlinarith

/-- Every explicit edge ends at a vertex. -/
theorem explicitTgtNum_lt {m j : ℕ} (hj : j < 2 * (q * (3 * k + 1) * m)) :
    explicitTgtNum k q m j < q * (3 * k + 2) + q * (3 * k + 1) * m := by
  unfold explicitTgtNum
  split_ifs <;> omega

/-- A number past the vertices has no ports. -/
theorem explicitPortsNum_eq_nil {m σ v : ℕ}
    (hv : q * (3 * k + 2) + q * (3 * k + 1) * m ≤ v) : explicitPortsNum k q m σ v = [] := by
  rw [explicitPortsNum, List.filter_eq_nil_iff]
  intro j hj
  rw [List.mem_range] at hj
  have h1 := explicitSrcNum_lt (σ := σ) hj
  have h2 := explicitTgtNum_lt hj
  simp only [decide_eq_true_eq, not_or]
  omega

/-- **The degree bound on numbers**: every vertex number has at most
`2 (3 k + 1) (letterBits k s b)` ports. -/
theorem length_explicitPortsNum_le {State : Type} (machine : MultiTapePTM k Bool State)
    (b : ℕ) [NeZero b] (e : State ≃ Fin s) (σ v : ℕ) :
    (explicitPortsNum k q (letterBits k s b) σ v).length ≤ 2 * (3 * k + 1) * letterBits k s b := by
  by_cases hv : v < q * (3 * k + 2) + q * (3 * k + 1) * letterBits k s b
  · have hmem : explicitPortsNum k q (letterBits k s b) σ v ∈
        (machine.explicitBlockNetwork [] b (scheduleOfNat k q σ) e).vertices.map Prod.fst := by
      rw [map_fst_vertices_explicitBlockNetwork]
      exact List.mem_map_of_mem (List.mem_range.mpr hv)
    obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
    rw [← hpv]
    exact ((machine.explicitBlockNetwork [] b (scheduleOfNat k q σ) e).length_le_maxDegree hp).trans
      (maxDegree_explicitBlockNetwork_le ..)
  · rw [explicitPortsNum_eq_nil (not_lt.mp hv)]
    exact Nat.zero_le _

end PortCounts

end Turing.MultiTapePTM
