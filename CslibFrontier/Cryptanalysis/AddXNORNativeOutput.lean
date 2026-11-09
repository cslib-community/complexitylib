/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeOutputBits
public import CslibFrontier.Cryptanalysis.AddXNORNativeSelectedClass
public import CslibFrontier.Computability.WordRAM.ListOutput
import all CslibFrontier.Cryptanalysis.AddXNORNativeOutputBits
import all CslibFrontier.Cryptanalysis.AddXNORNativeSelectedClass
import all CslibFrontier.Cryptanalysis.AddXNORNativeOrientedSearch
import all CslibFrontier.Computability.WordRAM.Structured

/-!
# Native list-valued dissection witnesses

The native serializer reads the actual orientation and packed witness registers,
subtracts the presence tag and writes oneReg zero/oneReg word per original operator.
A leading status word distinguishes a miss from a successful empty witness.
The length header and all output stores are native operations. This module does
not identify random-access word instructions with source multitape bit steps.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver.Output

open Cslib.WordRAM Quarter

/-- Serialization scratch avoids all four packed words, tag, direction and balance. -/
@[expose] def scratch : Fin 7 → Fin 40 := ![0, 1, 2, 4, 6, 7, 9]

private theorem scratch_injective : Function.Injective scratch := by decide

/-- Returned address of the length-prefixed output array. -/
abbrev result : Fin 40 := 39

/-- Packed-word scratch register. -/
abbrev valueReg := scratch OutputBits.value
/-- Remaining-count scratch register. -/
abbrev remainingReg := scratch OutputBits.remaining
/-- Output-cursor scratch register. -/
abbrev cursorReg := scratch OutputBits.cursor
/-- Constant-oneReg scratch register. -/
abbrev oneReg := scratch OutputBits.one

/-- Copy a packed register and serialize it, removing a presence tag when needed. -/
@[expose] def emitWord (n b : ℕ) (src : Fin 40) (untag back : Bool) : Code .standard 40 :=
  .seq (ram[ valueReg ← src; remainingReg ← #n;
      cursorReg ← #(if back then b + n - 1 else b); oneReg ← #1 ])
    (.seq (if untag then ram[ valueReg ← valueReg - oneReg ] else ram[ valueReg ← valueReg ])
      ((OutputBits.program back).rename scratch))

/-- Packed value after removing a possible presence tag. -/
def packedValue (x : Data 40) (src : Fin 40) (untag : Bool) : ℕ :=
  if untag then x.regs src - 1 else x.regs src

/-- Execute the actual register copy, tag subtraction and serialization loop. -/
theorem emitWord_exec {W n b : ℕ} (src : Fin 40) (untag back : Bool) (x : Data 40)
    (hx : x.Bounded W) (hfit : Fits W (b + n + 3)) :
    ∃ y, ExecWithin W (emitWord n b src untag back) x y (7 * n + 10) ∧
      Block.HoldsList b (OutputBits.words back n (packedValue x src untag)) y.mem ∧
      (∀ a, a < b ∨ b + n ≤ a → y.mem a = x.mem a) := by
  let u := x.set valueReg (x.regs src) |>.set remainingReg n
    |>.set cursorReg (if back then b + n - 1 else b) |>.set oneReg 1
  have hn : Fits W n := hfit.of_le (by omega)
  have hb : Fits W (if back then b + n - 1 else b) := hfit.of_le (by split <;> omega)
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have setup : ExecWithin (B := .standard) W
      (ram[ valueReg ← src; remainingReg ← #n;
      cursorReg ← #(if back then b + n - 1 else b); oneReg ← #1 ]) x u 4 := by
    ram_eval [u, hn, hb, h1, valueReg, remainingReg, cursorReg, oneReg, scratch, Fin.mk.injEq]
  let v := u.set valueReg (packedValue x src untag)
  have hpacked : Fits W (packedValue x src untag) := by
    cases untag
    · exact hx.1 src
    · exact (hx.1 src).of_le (Nat.sub_le _ _)
  have hsub : Fits W (x.regs src - 1) := (hx.1 src).of_le (Nat.sub_le _ _)
  have strip : ExecWithin (B := .standard) W
      (if untag then ram[ valueReg ← valueReg - oneReg ] else ram[ valueReg ← valueReg ])
      u v 1 := by
    cases untag <;>
      ram_eval [u, v, packedValue, hpacked, hsub, valueReg, remainingReg, cursorReg,
        oneReg, scratch,
        Fin.mk.injEq]
  obtain ⟨z, hz, contents, frame⟩ := OutputBits.exec back (v.comap scratch)
    (by simp +decide [v, u, valueReg, remainingReg, cursorReg, oneReg, scratch, Data.comap_regs])
    (by simp [v, valueReg, Data.comap_regs])
    (by simp +decide [v, u, valueReg, remainingReg, cursorReg, oneReg, scratch, Data.comap_regs])
    hpacked hfit
  let y := z.extend scratch v
  refine ⟨y, ?_, contents, frame⟩
  exact (setup.seq (strip.seq (hz.rename scratch_injective))).mono (by omega)

/-- The serializer never clobbers a live packed word or the high control bank. -/
theorem emitWord_preserves (n b : ℕ) (src : Fin 40) (untag back : Bool)
    (i : Fin 40) (hi : ∀ j, scratch j ≠ i) : (emitWord n b src untag back).Preserves i := by
  unfold emitWord
  simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  refine ⟨⟨hi _, hi _, hi _, hi _⟩, ?_, ?_⟩
  · cases untag <;>
      simpa only [Bool.false_eq_true, ↓reduceIte, Code.Preserves, Op.bin, Op.dest,
        ne_eq, Option.some.injEq] using hi OutputBits.value
  · exact Code.preserves_rename_of_forall_ne _ scratch _ hi

/-- Fixed metadata for a packed field: length, source register and presence tag. -/
abbrev Field := ℕ × Fin 40 × Bool

/-- Total number of emitted operators. -/
def fieldSize (fs : List Field) : ℕ := (fs.map Prod.fst).sum

/-- The concrete concatenation read from the original source registers. -/
def fieldWords (back : Bool) (fs : List Field) (x : Data 40) : List ℕ :=
  fs.flatMap fun f => OutputBits.words back f.1 (packedValue x f.2.1 f.2.2)

/-- Serialize consecutive fields. The dissection client always has exactly four
fields, so this construction does not unroll the variable operator counts. -/
@[expose] def emitFields (back : Bool) (b : ℕ) : List Field → Code .standard 40
  | [] => ram[ valueReg ← valueReg ]
  | f :: fs => .seq (emitWord f.1 b f.2.1 f.2.2 back) (emitFields back (b + f.1) fs)

/-- The represented field concatenation has the stated native array length. -/
theorem fieldWords_length (back : Bool) (fs : List Field) (x : Data 40) :
    (fieldWords back fs x).length = fieldSize fs := by
  simp only [fieldWords, List.length_flatMap, OutputBits.words_length, fieldSize]

/-- Consecutive actual stores serialize all protected packed registers. -/
theorem emitFields_exec {W b : ℕ} (back : Bool) (fs : List Field) (x : Data 40)
    (hx : x.Bounded W) (hfit : Fits W (b + fieldSize fs + 3))
    (hprotected : ∀ f ∈ fs, ∀ j, scratch j ≠ f.2.1) :
    ∃ y, ExecWithin W (emitFields back b fs) x y (7 * fieldSize fs + 10 * fs.length + 1) ∧
      Block.HoldsList b (fieldWords back fs x) y.mem ∧
      (∀ a, a < b ∨ b + fieldSize fs ≤ a → y.mem a = x.mem a) := by
  induction fs generalizing b x with
  | nil =>
    refine ⟨x, ?_, Block.holdsList_nil b x.mem, fun _ _ => rfl⟩
    simpa [emitFields, fieldSize, Data.set] using
      (ExecWithin.copy (B := .standard) (w := W) (d := valueReg) (s := valueReg) (x := x))
  | cons f fs ih =>
    have sizes : fieldSize (f :: fs) = f.1 + fieldSize fs := rfl
    obtain ⟨u, hu, left, uf⟩ := emitWord_exec (n := f.1) (b := b) f.2.1 f.2.2 back x hx
      (hfit.of_le (by rw [sizes]; omega))
    obtain ⟨y, hy, right, yf⟩ := ih (b := b + f.1) u (hu.bounded hx)
      (hfit.of_le (by rw [sizes]; omega))
      (fun g hg => hprotected g (List.mem_cons_of_mem f hg))
    have sources : fieldWords back fs u = fieldWords back fs x := by
      unfold fieldWords
      apply List.flatMap_congr
      intro g hg
      have keep := hu.regs_eq (emitWord_preserves f.1 b f.2.1 f.2.2 back g.2.1
        (hprotected g (List.mem_cons_of_mem f hg)))
      simp only [packedValue, keep]
    rw [sources] at right
    have first := left.frame (fun a ha hb => yf a (Or.inl (by
      rw [OutputBits.words_length] at hb; omega)))
    refine ⟨y, ?_, ?_, ?_⟩
    · apply (hu.seq hy).mono
      simp only [sizes, List.length_cons]
      omega
    · simpa only [fieldWords, List.flatMap_cons, OutputBits.words_length] using
        first.append (by simpa only [OutputBits.words_length, fieldWords] using right)
    · intro a ha
      rw [yf a (by rw [sizes] at ha; omega), uf a (by rw [sizes] at ha; omega)]

/-- The field serializer preserves registers outside scratch and the output pointer. -/
theorem emitFields_preserves (back : Bool) (b : ℕ) (fs : List Field)
    (i : Fin 40) (hi : ∀ j, scratch j ≠ i) :
    (emitFields back b fs).Preserves i := by
  induction fs generalizing b with
  | nil =>
    simpa only [emitFields, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      using hi OutputBits.value
  | cons f fs ih =>
    exact ⟨emitWord_preserves f.1 b f.2.1 f.2.2 back i hi, ih _⟩

/-- Original-order operator words read from the actual final register bank. -/
def operators (a b c d : ℕ) (x : Data 40) : List Bool :=
  if x.regs orientation = 1 then
    (decode a (x.regs (bank firstOperators))).reverse ++
      (decode b (x.regs (bank Quarter.operators))).reverse ++
      (decode c (x.regs (bank bits))).reverse ++ (decode d (x.regs tag - 1)).reverse
  else decode a (x.regs tag - 1) ++ decode b (x.regs (bank bits)) ++
    decode c (x.regs (bank Quarter.operators)) ++ decode d (x.regs (bank firstOperators))

/-- Every decoded operator is retained, including zeros and empty quarters. -/
theorem operators_length (a b c d : ℕ) (x : Data 40) : (operators a b c d x).length =
    a + b + c + d := by
  unfold operators
  split <;> simp [List.length_append, decode_length, Nat.add_assoc]

/-- The serialized operator list is exactly the original-chain witness observer. -/
theorem operators_zip {m : ℕ} (as bs cs ds : List (BitVec m)) (x : Data 40) :
    (operators as.length bs.length cs.length ds.length x).zip ((as ++ bs) ++ (cs ++ ds)) =
      witness as bs cs ds x := by
  unfold operators witness orientedWitness
  by_cases h : x.regs orientation = 1
  all_goals simp only [h, decide_true, decide_false, ↓reduceIte,
    Bool.false_eq_true, Data.comap_regs]
  all_goals simp only [List.append_assoc]
  all_goals rw [List.zip_append (by simp only [List.length_reverse, decode_length]),
    List.zip_append (by simp only [List.length_reverse, decode_length]),
    List.zip_append (by simp only [List.length_reverse, decode_length])]

/-- Registers retaining the complete witness interpretation and computed balance. -/
def Live (i : Fin 40) : Prop :=
  i = tag ∨ i = bank bits ∨ i = bank Quarter.operators ∨ i = bank firstOperators ∨
    i = orientation ∨ i = balance

private theorem live_scratch (i : Fin 40) (hi : Live i) : ∀ j, scratch j ≠ i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem live_result (i : Fin 40) (hi : Live i) : result ≠ i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exactly four packed fields in original quarter order in either orientation. -/
@[expose] def fields (a b c d : ℕ) (back : Bool) : List Field :=
  if back then [(a, bank firstOperators, false), (b, bank Quarter.operators, false),
    (c, bank bits, false), (d, tag, true)]
  else [(a, tag, true), (b, bank bits, false), (c, bank Quarter.operators, false),
    (d, bank firstOperators, false)]

private theorem fields_size (a b c d : ℕ) (back : Bool) :
    fieldSize (fields a b c d back) = a + b + c + d := by
  cases back <;> simp [fields, fieldSize, Nat.add_assoc]

private theorem fields_length (a b c d : ℕ) (back : Bool) :
    (fields a b c d back).length = 4 := by cases back <;> rfl

private theorem fields_protected (a b c d : ℕ) (back : Bool) :
    ∀ f ∈ fields a b c d back, ∀ j, scratch j ≠ f.2.1 := by
  intro f hf
  apply live_scratch
  cases back <;> simp only [fields, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  all_goals rcases hf with rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
    exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

private theorem operators_frame (a b c d : ℕ) (x y : Data 40)
    (h : ∀ i, Live i → y.regs i = x.regs i) : operators a b c d y = operators a b c d x := by
  simp only [operators, h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)),
    h _ (Or.inr (Or.inr (Or.inl rfl))), h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]

/-- Actual stores for the output length and leading status word. -/
@[expose] def header (D n : ℕ) (present : Bool) : Code .standard 40 := ram[
  result ← #D; valueReg ← #(n + 1); *result ← valueReg; cursorReg ← #(D + 1);
  valueReg ← #present.toNat; *cursorReg ← valueReg ]

private theorem header_preserves (D n : ℕ) (present : Bool) (i : Fin 40) (hi : Live i) :
    (header D n present).Preserves i := by
  simp only [header, Code.Preserves, Op.dest, ne_eq, Option.some.injEq,
    reduceCtorEq, not_false_eq_true, true_and, and_true]
  exact ⟨live_result i hi, live_scratch i hi _, live_scratch i hi _, live_scratch i hi _⟩

private theorem header_exec {W D n : ℕ} (present : Bool) (x : Data 40)
    (hfit : Fits W (D + n + 6)) :
    ∃ y, ExecWithin W (header D n present) x y 6 ∧
      y.mem D = n + 1 ∧ y.mem (D + 1) = present.toNat ∧ y.regs result = D ∧
      (∀ a, a ≠ D → a ≠ D + 1 → y.mem a = x.mem a) := by
  let y := x.set result D |>.set valueReg (n + 1) |>.write D (n + 1)
    |>.set cursorReg (D + 1) |>.set valueReg present.toNat |>.write (D + 1) present.toNat
  have hD : Fits W D := hfit.of_le (by omega)
  have hn : Fits W (n + 1) := hfit.of_le (by omega)
  have ha : Fits W (D + 1) := hfit.of_le (by omega)
  have hp : Fits W present.toNat := hfit.of_le (by cases present <;> simp)
  have he : ExecWithin W (header D n present) x y 6 := by
    ram_eval [header, y, hD, hn, ha, hp, result, valueReg, cursorReg, scratch, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, ?_⟩
  · simp [y, Data.write_mem]
  · simp [y, Data.write_mem]
  · simp +decide [y, result, valueReg, cursorReg, scratch]
  · intro a ha hb
    simp only [y, Data.write_mem, Data.set_mem, Function.update_of_ne ha,
      Function.update_of_ne hb]

/-- Native hit/miss and direction branches, then four fixed serialization loops. -/
@[expose] def program (D a b c d : ℕ) : Code .standard 40 :=
  .seq (ram[ valueReg ← #0 ])
    (.branch (.lt valueReg tag)
      (.seq (header D (a + b + c + d) true)
        (.seq (ram[ oneReg ← #1 ])
          (.branch (.eq orientation oneReg)
            (emitFields true (D + 2) (fields a b c d true))
            (emitFields false (D + 2) (fields a b c d false)))))
      (header D 0 false))

/-- Concrete output words: a status, followed by original-order operator bits. -/
def outputWords (a b c d : ℕ) (x : Data 40) : List ℕ :=
  if x.regs tag = 0 then [0] else 1 :: (operators a b c d x).map Bool.toNat

private theorem fields_words (a b c d : ℕ) (x : Data 40) (back : Bool)
    (h : (x.regs orientation = 1) ↔ back = true) :
    fieldWords back (fields a b c d back) x = (operators a b c d x).map Bool.toNat := by
  cases back <;> simp [fields, fieldWords, packedValue, OutputBits.words, operators, h,
    List.map_append]

/-- Complete native serializer, with no supplied witness-correctness conclusion.
The output convention is `[0]` on a miss and `1 :: operators` on a hit. -/
theorem exec {W D a b c d : ℕ} (x : Data 40) (hx : x.Bounded W)
    (hfit : Fits W (D + (a + b + c + d) + 6)) :
    ∃ y, ExecWithin W (program D a b c d) x y (7 * (a + b + c + d) + 53) ∧
      outputList y.mem D = outputWords a b c d x ∧ y.regs result = D ∧
      (∀ i, Live i → y.regs i = x.regs i) ∧
      (∀ addr, addr < D ∨ D + (a + b + c + d) + 2 ≤ addr → y.mem addr = x.mem addr) := by
  let z := x.set valueReg 0
  have init : ExecWithin (B := .standard) W (ram[ valueReg ← #0 ]) x z 1 :=
    ExecWithin.const (fits_zero W)
  have zlive (i : Fin 40) (hi : Live i) : z.regs i = x.regs i :=
    init.regs_eq (by simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
      using live_scratch i hi OutputBits.value)
  have ztag : z.regs tag = x.regs tag := zlive _ (Or.inl rfl)
  have zv : z.regs valueReg = 0 := by simp [z]
  by_cases hit : x.regs tag ≠ 0
  · obtain ⟨u, hu, length, status, pointer, frame⟩ := header_exec true z hfit
    let v := u.set oneReg 1
    have vone : v.regs oneReg = 1 := by simp [v]
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have flag : ExecWithin (B := .standard) W (ram[ oneReg ← #1 ]) u v 1 := .const h1
    have headerLive (i : Fin 40) (hi : Live i) : u.regs i = x.regs i :=
      (hu.regs_eq (header_preserves _ _ _ i hi)).trans (zlive i hi)
    have vlive (i : Fin 40) (hi : Live i) : v.regs i = x.regs i :=
      (flag.regs_eq (by simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        using live_scratch i hi OutputBits.one)).trans (headerLive i hi)
    have run (back : Bool) (dir : (x.regs orientation = 1) ↔ back = true) :
        ∃ y, ExecWithin W (emitFields back (D + 2) (fields a b c d back)) v y
            (7 * (a + b + c + d) + 41) ∧
          outputList y.mem D = outputWords a b c d x ∧ y.regs result = D ∧
          (∀ i, Live i → y.regs i = x.regs i) ∧
          (∀ addr, addr < D ∨ D + (a + b + c + d) + 2 ≤ addr →
            y.mem addr = x.mem addr) := by
      obtain ⟨y, hy, contents, yf⟩ := emitFields_exec (b := D + 2) back (fields a b c d back) v
        (flag.bounded (hu.bounded (init.bounded hx)))
        (hfit.of_le (by rw [fields_size]; omega)) (fields_protected _ _ _ _ _)
      have live (i : Fin 40) (hi : Live i) : y.regs i = x.regs i :=
        (hy.regs_eq (emitFields_preserves _ _ _ i (live_scratch i hi))).trans (vlive i hi)
      have yp : y.regs result = D :=
        (hy.regs_eq (emitFields_preserves _ _ _ result (by decide))).trans
          ((flag.regs_eq (by decide)).trans pointer)
      have preserved (addr : ℕ) (ha : addr = D ∨ addr = D + 1) : y.mem addr = u.mem addr :=
        yf addr (Or.inl (by omega))
      have bodyWords : fieldWords back (fields a b c d back) v =
          (operators a b c d x).map Bool.toNat := by
        rw [fields_words _ _ _ _ v back (by rw [vlive _ (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact dir)]
        rw [operators_frame _ _ _ _ x v vlive]
      rw [bodyWords] at contents
      refine ⟨y, ?_, ?_, ?_, live, ?_⟩
      · exact hy.mono (by rw [fields_size, fields_length])
      · apply outputList_eq_iff.mpr
        constructor
        · rw [preserved _ (Or.inl rfl), length]
          simp only [outputWords, hit, ↓reduceIte, List.length_cons, List.length_map,
            operators_length]
        · have first : Block.HoldsList (D + 1) [1] y.mem := by
            intro i
            have hi : i.val = 0 := by
              have := i.isLt
              simp only [List.length_singleton] at this
              omega
            change y.mem (D + 1 + i.val) = [1][i.val]
            simp only [hi, Nat.add_zero, List.getElem_cons_zero]
            rw [preserved _ (Or.inr rfl), status]
            rfl
          simpa only [outputWords, hit, ↓reduceIte, List.singleton_append,
            List.length_singleton, Nat.add_assoc] using first.append contents
      · exact yp
      · intro addr ha
        rw [yf addr (by rw [fields_size]; omega)]
        exact frame addr (by omega) (by omega)
    by_cases dir : x.regs orientation = 1
    · obtain ⟨y, hy, rest⟩ := run true (by simp [dir])
      refine ⟨y, ?_, rest⟩
      have cond : (Cond.eq orientation oneReg).Holds v := by
        rw [Cond.holds_eq, vone, vlive _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
        exact dir
      have branch := ExecWithin.branch_pos (neg := emitFields false (D + 2)
        (fields a b c d false)) cond hy
      exact (init.seq (ExecWithin.branch_pos
        (by simp only [Cond.holds_lt, zv, ztag]; omega)
        (hu.seq (flag.seq branch)))).mono (by omega)
    · obtain ⟨y, hy, rest⟩ := run false (by simp [dir])
      refine ⟨y, ?_, rest⟩
      have cond : ¬(Cond.eq orientation oneReg).Holds v := by
        rw [Cond.holds_eq, vone, vlive _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
        exact dir
      have branch := ExecWithin.branch_neg (pos := emitFields true (D + 2)
        (fields a b c d true)) cond hy
      exact (init.seq (ExecWithin.branch_pos
        (by simp only [Cond.holds_lt, zv, ztag]; omega)
        (hu.seq (flag.seq branch)))).mono (by omega)
  · have miss : x.regs tag = 0 := by omega
    obtain ⟨y, hy, length, status, pointer, frame⟩ := header_exec (D := D) (n := 0) false z
      (hfit.of_le (by omega))
    refine ⟨y, ?_, ?_, pointer, ?_, ?_⟩
    · exact (init.seq (ExecWithin.branch_neg
        (by simp only [Cond.holds_lt, zv, ztag]; omega)
        hy)).mono (by omega)
    · rw [outputWords, ite_eq_left miss]
      apply outputList_eq_iff.mpr
      refine ⟨length, ?_⟩
      intro i
      have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      change y.mem (D + 1 + i.val) = [0][i.val]
      simp only [hi, Nat.add_zero, List.getElem_cons_zero]
      exact status
    · intro i hi
      exact (hy.regs_eq (header_preserves _ _ _ i hi)).trans (zlive i hi)
    · intro addr ha
      exact frame addr (by omega) (by omega)

private theorem emitWord_size (n b : ℕ) (src : Fin 40) (untag back : Bool) :
    (emitWord n b src untag back).size = 16 := by
  cases untag <;> cases back <;> rfl

private theorem emitFields_size (back : Bool) (b : ℕ) (fs : List Field) :
    (emitFields back b fs).size = 16 * fs.length + 1 := by
  induction fs generalizing b with
  | nil => rfl
  | cons f fs ih =>
    simp only [emitFields, Code.size, emitWord_size, ih, List.length_cons]
    omega

/-- Output has fixed graph size, independent of lengths, packed values and direction. -/
theorem program_size (D a b c d : ℕ) : (program D a b c d).size = 148 := by
  simp only [program, header, Code.size, emitFields_size, fields_length]


end Cslib.Cryptanalysis.AddXNOR.Native.Driver.Output
