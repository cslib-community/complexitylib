/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeSelectedClass
public import Complexity.Computability.WordRAM.RegisterParameters
import all Complexity.Cryptanalysis.AddXNORNativeSelectedClass
import all Complexity.Cryptanalysis.AddXNORNativeClassSearch
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch

/-!
# Register-selected native class execution

The enclosing controller supplies the current class and its complemented key in
preserved registers. Only the corresponding immediate writes are replaced by
copies; the proved native construction, orientation, witness and release run is
reused with exactly the same final data and instruction bound.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Current low-bit class, maintained by the outer loop. -/
abbrev classIndex : Fin 40 := 36
/-- Complemented low-bit key, computed before native class selection. -/
abbrev inverseIndex : Fin 40 := 37
/-- Native-computed exclusive bound for the outer class loop. -/
abbrev classLimit : Fin 40 := 39

private theorem bank_ne_high (r : Fin 40) (hr : 32 ≤ r.val) (i : Fin 32) : bank i ≠ r := by
  intro h
  have hi := i.isLt
  have hv := congrArg (fun j : Fin 40 => j.val) h
  change i.val = r.val at hv
  omega

/-- The class-layout transfer takes its class value from a preserved register. -/
@[expose] def registerLayout (key : Fin 40) (b q n M N h D : ℕ) : Code .standard 40 :=
  .seq (.op (.const (bank fullBase) b))
    (.seq (.op (.const (bank projectedBase) q))
      (.seq (.op (.const (bank count) n))
        (.seq (.op (.const (bank fullModulus) M))
          (.seq (.op (.const (bank projectedModulus) N))
            (.seq (.op (.copy (bank Quarter.initial) key))
              ((ram[ heads ← #h; Dictionary.table ← #D ] : Code .standard 32).rename bank))))))

/-- The two native middle-quarter loops share the preserved class register. -/
@[expose] def registerPrepared (key : Fin 40) (c n₂ b₃ n₃ q₂ q₃ M N h h₄ D : ℕ) :
    Code .standard 40 :=
  .seq (registerLayout key c q₂ n₂ M N h D)
    (.seq (retainClass.rename bank) (.seq (registerLayout key b₃ q₃ n₃ M N h₄ D)
      (.seq ((ram[ Quarter.one ← #1; stop ← Quarter.one <<< count ] :
          Code .standard 32).rename bank)
        (probeClass.rename bank))))

/-- Actual native quarter construction and register-selected class search. -/
@[expose] def registerKernel {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : ℕ) (key : Fin 40) (back : Bool) : Code .standard 40 :=
  if back then
    .seq ((projectMiddle L.b₃ c L.b₂ b L.q₂ L.q₃ (2 ^ p)).rename bank)
      (.seq ((prepareClassBuckets L.b₄ d L.b₁ a (2 ^ m) s t L.h L.f L.h₄ L.f₄ (2 ^ p)).rename bank)
        (registerPrepared key L.b₃ c L.b₂ b L.q₂ L.q₃ (2 ^ m) (2 ^ p) L.h L.h₄ L.D))
  else
    .seq ((projectMiddle L.b₂ b L.b₃ c L.q₂ L.q₃ (2 ^ p)).rename bank)
      (.seq ((prepareClassBuckets L.b₁ a L.b₄ d (2 ^ m) s t L.h L.f L.h₄ L.f₄ (2 ^ p)).rename bank)
        (registerPrepared key L.b₂ b L.b₃ c L.q₂ L.q₃ (2 ^ m) (2 ^ p) L.h L.h₄ L.D))

/-- A complete register-selected lifetime includes physical dictionary release. -/
@[expose] def registerCycle {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : ℕ) (key : Fin 40) (back : Bool) : Code .standard 40 :=
  .seq (registerKernel L s t key back) (releaseWitness.rename bank)

/-- Only class-value writes change; all native subroutines are the proved ones. -/
theorem registerCycle_parameter {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t g : ℕ) (key : Fin 40) (hk : 32 ≤ key.val) (back : Bool) :
    Code.RegisterParameter key g ((orientedCycle L s t g back).rename bank)
      (registerCycle L s t key back) := by
  cases back <;>
    unfold orientedCycle orientedKernel registerCycle registerKernel searchClass
      searchPreparedClass registerPrepared classLayout registerLayout
  all_goals
    repeat' first
      | exact .same _ (Code.preserves_rename_of_forall_ne _ bank _ (bank_ne_high key hk))
      | apply Code.RegisterParameter.copy; exact bank_ne_high key hk _
      | apply Code.RegisterParameter.seq

/-- Load actual table cells and dispatch to the native orientation using the
current class registers, with no class-dependent code generation. -/
@[expose] def registerSelected {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : Code .standard 40 :=
  .seq (ram[ countAddress ← classIndex; countAddress ← forwardPointer + countAddress;
    forwardValue ← *countAddress; countAddress ← inverseIndex;
    countAddress ← backwardPointer + countAddress; backwardValue ← *countAddress ])
    (.branch (.lt backwardValue forwardValue)
      (.seq (ram[ orientation ← #1 ]) (registerCycle L (~~~t).toNat (~~~s).toNat inverseIndex true))
      (.seq (ram[ orientation ← #0 ]) (registerCycle L s.toNat t.toNat classIndex false)))

/-- Register-selected class execution preserves every enclosing high register. -/
theorem registerCycle_preserves {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : ℕ) (key : Fin 40) (hk : 32 ≤ key.val) (back : Bool)
    (i : Fin 40) (hi : 32 ≤ i.val) : (registerCycle L s t key back).Preserves i :=
  (registerCycle_parameter L s t 0 key hk back).preserves_iff i |>.mpr
    (cycle_preserves L s t 0 back i hi)

private def halfSelected {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) (g : BitVec p) : Code .standard 40 :=
  .seq (ram[ countAddress ← classIndex; countAddress ← forwardPointer + countAddress;
    forwardValue ← *countAddress; countAddress ← #(~~~g).toNat;
    countAddress ← backwardPointer + countAddress; backwardValue ← *countAddress ])
    (.branch (.lt backwardValue forwardValue)
      (.seq (ram[ orientation ← #1 ])
        ((orientedCycle L (~~~t).toNat (~~~s).toNat (~~~g).toNat true).rename bank))
      (.seq (ram[ orientation ← #0 ]) (registerCycle L s.toNat t.toNat classIndex false)))

/-- Reuse the full immediate-parameter execution after computing both actual
class registers. The result, witness and memory are identical, instruction for
instruction; no semantic query, direction or dictionary premise is introduced. -/
theorem registerSelected_exec {W m p a b c d T : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) (g : BitVec p) (x y : Data 40)
    (hg : x.regs classIndex = g.toNat) (hng : x.regs inverseIndex = (~~~g).toNat)
    (he : ExecWithin W (selectedClass L s t g) x y T) :
    ExecWithin W (registerSelected L s t) x y T := by
  have first : Code.RegisterParameter classIndex g.toNat
      (selectedClass L s t g) (halfSelected L s t g) := by
    unfold selectedClass halfSelected
    repeat' first
      | exact registerCycle_parameter _ _ _ _ _ (by decide) _
      | exact .same _ (cycle_preserves _ _ _ _ _ _ (by decide))
      | exact .same _ (by
          simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
          decide)
      | apply Code.RegisterParameter.copy; decide
      | apply Code.RegisterParameter.seq
      | apply Code.RegisterParameter.branch
  have second : Code.RegisterParameter inverseIndex (~~~g).toNat
      (halfSelected L s t g) (registerSelected L s t) := by
    unfold halfSelected registerSelected
    repeat' first
      | exact registerCycle_parameter _ _ _ _ _ (by decide) _
      | exact .same _ (registerCycle_preserves _ _ _ _ (by decide) _ _ (by decide))
      | exact .same _ (by
          simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
          decide)
      | apply Code.RegisterParameter.copy; decide
      | apply Code.RegisterParameter.seq
      | apply Code.RegisterParameter.branch
  exact second.execWithin hng (first.execWithin hg he)

/-- The dynamic selector leaves the class index and exclusive bound available to
its native enclosing loop. -/
theorem registerSelected_preserves {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) (i : Fin 40) (hi : i = classIndex ∨ i = inverseIndex ∨ i = classLimit) :
    (registerSelected L s t).Preserves i := by
  unfold registerSelected
  simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · rcases hi with rfl | rfl | rfl <;> decide
  · constructor <;> constructor
    · rcases hi with rfl | rfl | rfl <;> decide
    · apply registerCycle_preserves _ _ _ _ (by decide) _
      rcases hi with rfl | rfl | rfl <;> decide
    · rcases hi with rfl | rfl | rfl <;> decide
    · apply registerCycle_preserves _ _ _ _ (by decide) _
      rcases hi with rfl | rfl | rfl <;> decide

private theorem projectMiddle_size (a b c d e f g : ℕ) :
    (projectMiddle a b c d e f g).size = 34 := by rfl

private theorem prepareBuckets_size (a b c d e f g h i j k l : ℕ) :
    (prepareClassBuckets a b c d e f g h i j k l).size = 127 := by rfl

private theorem retainClass_size : retainClass.size = 100 := by rfl

private theorem probeClass_size : probeClass.size = 96 := by rfl

private theorem releaseWitness_size : releaseWitness.size = 18 := by rfl

/-- Register selection changes immediate values, never the class lifetime's
instruction graph or compiled code size. -/
theorem registerCycle_size {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : ℕ) (key : Fin 40) (back : Bool) : (registerCycle L s t key back).size = 393 := by
  cases back <;>
    simp only [registerCycle, registerKernel, registerPrepared, registerLayout,
      Bool.false_eq_true, ↓reduceIte, Code.size, Code.size_rename,
      projectMiddle_size, prepareBuckets_size, retainClass_size, probeClass_size,
      releaseWitness_size]

/-- The native table-selected class dispatch has one fixed instruction graph. -/
theorem registerSelected_size {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (s t : BitVec m) : (registerSelected L s t).size = 796 := by
  simp only [registerSelected, Code.size, registerCycle_size]

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
