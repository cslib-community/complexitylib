/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeClassLoop
import all Complexity.Cryptanalysis.AddXNORNativeClassLoop
import all Complexity.Cryptanalysis.AddXNORNativeCounterPair
import all Complexity.Cryptanalysis.AddXNORNativeSelectedClass
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch

/-!
# Original-input native dissection with computed orientation and class composition

Construct both counter tables and their maximum of minima before storing any
full-width class. Actual counter loads select the forward or conjugated inverse
search at every class. Each class releases its dictionary, and native conditional
composition covers all low-bit classes unless an actual original witness is found.

This gives functional and finite instruction-time components of
[WangLvShenZhang2027], Theorem 7, PDF p. 22. The outer controller is a fixed-size
native loop with a computed range. A simultaneous prefix-space bound in terms of
the computed balance, derived global word width and the source sorted-list
multitape bit model remain separate.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Counter preprocessing has its own disjoint scratch interval below the class
workspaces. All fields are raw addresses, separation or physical word capacity. -/
structure CounterLayout {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d) where
  /-- Original contiguous forward-half and reversed suffix array bases. -/
  prefixBase : ℕ
  /-- Original reversed suffix input base. -/
  suffixBase : ℕ
  /-- Projection buffers and two reusable counter-buffer pairs. -/
  q : ℕ
  /-- First pair of reusable counter buffers. -/
  B : ℕ
  /-- Reversed suffix projection scratch base. -/
  r : ℕ
  /-- Second pair of reusable counter buffers. -/
  C : ℕ
  prefixEnd : prefixBase + (a + b) ≤ q
  suffixEnd : suffixBase + (c + d) ≤ q
  firstEnd : L.b₁ + a ≤ q
  secondEnd : L.b₂ + b ≤ q
  thirdEnd : L.b₃ + c ≤ q
  fourthEnd : L.b₄ + d ≤ q
  projection : q + (a + b) ≤ B
  separation : B + 2 * 2 ^ p ≤ r
  projectionBack : r + (c + d) ≤ C
  below : C + 2 * 2 ^ p ≤ L.q₂
  capacityForward : Fits W (prefixBase + q + 2 * B + (a + b) +
    4 * 2 ^ p + 2 * 2 ^ (a + b) + 2 ^ m + 12)
  capacityBackward : Fits W (suffixBase + r + 2 * C + (c + d) +
    4 * 2 ^ p + 2 * 2 ^ (c + d) + 2 ^ m + 12)
  capacityScan : Fits W (B + C + 3 * 2 ^ p + 2)

/-- The computed count observer is the existing manuscript balance parameter,
with no new balance assumption or independent notion of solution count. -/
theorem computedBalance_eq_classBalance {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    computedBalance (p := p) as bs cs ds s t =
      classBalance p (Fin.append as.get bs.get) (Fin.append cs.get ds.get) s t := by
  apply Finset.sup_congr rfl
  intro g _
  have hf := WordTable.projected_classCounters hp (Fin.append as.get bs.get) s g
  have hb := WordTable.projected_backwardCounters hp (Fin.append cs.get ds.get) t g
  change (WordTable.classCounters (List.ofFn ((BitVec.setWidth p) ∘
    Fin.append as.get bs.get)) (s.setWidth p)).read g = _ at hf
  change (WordTable.backwardCounters (List.ofFn ((BitVec.setWidth p) ∘
    Fin.append cs.get ds.get)) (t.setWidth p)).read g = _ at hb
  have hf' : forwardCount as bs s g = forwardClassCount p (Fin.append as.get bs.get) s g := by
    simpa only [forwardCount, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get] using hf
  have hb' : backwardCount cs ds t g = backwardClassCount p (Fin.append cs.get ds.get) t g := by
    simpa only [backwardCount, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get] using hb
  rw [hf', hb']

/-- The count selected by the actual comparison is the minimum, bounded by the
computed maximum. This is a selected multiplicity bound, not compiled peak space. -/
theorem selected_count_le_balance {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) :
    (if backwardCount cs ds t g < forwardCount as bs s g then backwardCount cs ds t g
      else forwardCount as bs s g) ≤ computedBalance (p := p) as bs cs ds s t := by
  have h := Finset.le_sup (f := fun g : BitVec p =>
    min (forwardCount as bs s g) (backwardCount cs ds t g)) (Finset.mem_univ g)
  split
  · rwa [min_eq_right (by omega)] at h
  · rwa [min_eq_left (by omega)] at h

/-- Actual native preprocessing followed by all selected class lifetimes. -/
@[expose] def dissection {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (K : CounterLayout L) (s t : BitVec m) : Code .standard 40 :=
  .seq (prepare K.prefixBase (a + b) K.suffixBase (c + d) K.q K.B K.r K.C
    (2 ^ p) (s.setWidth p).toNat ((~~~t).setWidth p).toNat)
    (searchLoop L s t)

private theorem prepare_size (a n b k q B r C N s t : ℕ) :
    (prepare a n b k q B r C N s t).size = 148 := by rfl

/-- Counter construction, balance and the uniform class loop together have fixed
compiled code size; immediates vary with scalar parameters, the graph does not. -/
theorem dissection_size {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (K : CounterLayout L) (s t : BitVec m) : (dissection L K s t).size = 960 := by
  simp only [dissection, Code.size, prepare_size, searchLoop_size]

/-- Appending the charged final halt produces a fixed 961-instruction program. -/
theorem dissection_program_length {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (K : CounterLayout L) (s t : BitVec m) : ((dissection L K s t).program tag).length = 961 := by
  simp only [Code.program, List.length_append, Code.length_assemble, dissection_size,
    List.length_cons, List.length_nil]

/-- Charged setup budget including both projections, counter constructions and
balance scan. This is a count of actual standard WordRAM instructions. -/
def prepareTime (p a b : ℕ) : ℕ :=
  (((10 * a + 8) + (6 + (4 * 2 ^ p + a * (14 * 2 ^ p + 14) + 10))) +
    (1 + (((10 * b + 8) + (6 + (4 * 2 ^ p + b * (14 * 2 ^ p + 14) + 10))) + 1))) +
    (14 * 2 ^ p + 11)

/-- Simultaneous occupied cells: preprocessing is charged once, and the largest
selected retained class allowance is reused after each native release. -/
def dissectionSpace {m p : ℕ} (D : ℕ) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) : ℕ :=
  D + prepareTime p (as.length + bs.length) (cs.length + ds.length) +
    lifetimeStores (p := p) as bs cs ds s t

/-- Exact balance semantics of a ready native table pair. -/
theorem ready_balance_eq {W m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (x : Data 40)
    (hr : Ready as bs cs ds s t L x) :
    Balance.prefixMax x.mem (x.regs forwardPointer) (x.regs backwardPointer) (2 ^ p) (2 ^ p) =
      computedBalance (p := p) as bs cs ds s t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    let g : BitVec p := BitVec.ofNatLT j hj'
    have hg : g.toNat = j := rfl
    have hh := Finset.le_sup (f := fun g : BitVec p =>
      min (forwardCount as bs s g) (backwardCount cs ds t g)) (Finset.mem_univ g)
    rw [← hr.1 g, ← hr.2.1 g, BitVec.toNat_not, hg] at hh
    exact hh
  · apply Finset.sup_le
    intro g _
    rw [← hr.1 g, ← hr.2.1 g, BitVec.toNat_not]
    exact Finset.le_sup (f := fun j => min (x.mem (x.regs forwardPointer + j))
      (x.mem (x.regs backwardPointer + (2 ^ p - 1 - j)))) (Finset.mem_range.mpr g.isLt)

/-- Complete original-array native decision and witness execution. Counter
contents, balance, orientation, dictionary validity, traversal and termination
are all conclusions of the actual constructed program, never premises. Raw
contiguous half arrays may alias the corresponding four quarter arrays. -/
theorem dissection_exec {W m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (L : SearchLayout W m p as.length bs.length cs.length ds.length) (K : CounterLayout L)
    (x : Data 40) (hx : L.Raw as bs cs ds (x.comap bank))
    (hprefix : ∀ i (hi : i < (as ++ bs).length),
      x.mem (K.prefixBase + i) = (as ++ bs)[i].toNat)
    (hsuffix : ∀ i (hi : i < (cs ++ ds).reverse.length),
      x.mem (K.suffixBase + i) = (cs ++ ds).reverse[i].toNat)
    (hfit : Fits W (L.D + 4 * 2 ^ m + 8))
    (hload : Fits W (2 * L.q₂ + 2 * 2 ^ p + 4)) :
    ∃ y, ExecWithin W (dissection L K s t) x y
        (prepareTime p (as.length + bs.length) (cs.length + ds.length) +
          (5 + loopTime (p := p) as bs cs ds s t 0 (2 ^ p))) ∧
      SpaceWithin W (dissection L K s t) x y
        (prepareTime p (as.length + bs.length) (cs.length + ds.length) +
          (5 + loopTime (p := p) as bs cs ds s t 0 (2 ^ p)))
        (dissectionSpace (p := p) L.D as bs cs ds s t) ∧
      (y.regs tag ≠ 0 ↔ ∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag = 0 ↔ ¬∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs balance = computedBalance (p := p) as bs cs ds s t ∧
      L.Raw as bs cs ds (y.comap bank) := by
  obtain ⟨u, hu, uf, ur, _, ub, uz, up, uq, frame⟩ := prepare_exec
    (p := p) (as ++ bs) (cs ++ ds).reverse s (~~~t) x hprefix hsuffix
    (by simpa only [List.length_append] using K.prefixEnd)
    (by simpa only [List.length_reverse, List.length_append] using K.suffixEnd)
    (by simpa only [List.length_append] using K.projection) K.separation
    (by simpa only [List.length_reverse, List.length_append] using K.projectionBack)
    (by simpa only [List.length_append] using K.capacityForward)
    (by simpa only [List.length_reverse, List.length_append] using K.capacityBackward)
    K.capacityScan
  have qr : K.q ≤ K.r := calc
    K.q ≤ K.q + (as.length + bs.length) := Nat.le_add_right _ _
    _ ≤ K.B := K.projection
    _ ≤ K.B + 2 * 2 ^ p := Nat.le_add_right _ _
    _ ≤ K.r := K.separation
  have rC : K.r ≤ K.C := (Nat.le_add_right _ _).trans K.projectionBack
  have qD : L.q₂ ≤ L.D := calc
    L.q₂ ≤ L.q₂ + bs.length + cs.length := by omega
    _ ≤ L.q₃ := L.project₂
    _ ≤ L.q₃ + bs.length + cs.length := by omega
    _ ≤ L.h := L.project₃
    _ ≤ L.h + 2 ^ p := Nat.le_add_right _ _
    _ ≤ L.f := L.heads
    _ ≤ L.f + 3 * (2 ^ as.length + 2 ^ ds.length) := Nat.le_add_right _ _
    _ ≤ L.h₄ := L.arena
    _ ≤ L.h₄ + 2 ^ p := Nat.le_add_right _ _
    _ ≤ L.f₄ := L.heads₄
    _ ≤ L.f₄ + 3 * (2 ^ as.length + 2 ^ ds.length) := Nat.le_add_right _ _
    _ ≤ L.D := L.boundary
  have raw : L.Raw as bs cs ds (u.comap bank) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [Data.comap_mem, frame _ (Or.inl (by have := K.firstEnd; omega))]
      exact hx.1 i hi
    · intro i hi
      rw [Data.comap_mem, frame _ (Or.inl (by have := K.secondEnd; omega))]
      exact hx.2.1 i hi
    · intro i hi
      rw [Data.comap_mem, frame _ (Or.inl (by
        have := K.thirdEnd; simp only [List.length_reverse] at hi; omega))]
      exact hx.2.2.1 i hi
    · intro i hi
      rw [Data.comap_mem, frame _ (Or.inl (by
        have := K.fourthEnd; simp only [List.length_reverse] at hi; omega))]
      exact hx.2.2.2.1 i hi
    · intro a ha
      rw [Data.comap_mem, frame _ (Or.inr (K.below.trans (qD.trans ha)))]
      exact hx.2.2.2.2 a ha
  have ready : Ready as bs cs ds s t L u := by
    refine ⟨uf, ?_, ?_, ?_, uz⟩
    · intro g
      have h := ur (~~~g)
      simpa only [Counters.Represents, List.map_reverse, BitVec.setWidth_not hp,
        WordTable.backwardCounters_conjugate, backwardCount] using h
    · rcases up with h | h <;> rw [h] <;> have := K.separation <;> have := K.below <;> omega
    · rcases uq with h | h <;> rw [h] <;> have := K.below <;> omega
  have mu : u.regs balance = computedBalance (p := p) as bs cs ds s t :=
    ub.trans (ready_balance_eq as bs cs ds s t L u ready)
  obtain ⟨y, hy, space, hit, sound, _, _, _, yr, _, yb⟩ := searchLoop_exec hp as bs cs ds s t L
    u raw ready hfit hload
  have iffhit := hit
  refine ⟨y, ?_, ?_, iffhit, ?_, sound, yb.trans mu, yr⟩
  · simpa only [dissection, prepareTime, List.length_append, List.length_reverse] using hu.seq hy
  · have prepSpace := hu.stores.space
      (x.supportLe_of_zero_tail (fun a ha => hx.2.2.2.2 a ha))
    have prepBound := prepSpace.mono le_rfl
      (show L.D + _ ≤ dissectionSpace (p := p) L.D as bs cs ds s t by
        simp only [dissectionSpace, prepareTime, List.length_append, List.length_reverse]
        omega)
    have searchBound := space.mono le_rfl
      (show L.D + _ ≤ dissectionSpace (p := p) L.D as bs cs ds s t by
        dsimp only [dissectionSpace]; omega)
    simpa only [dissection, prepareTime, List.length_append, List.length_reverse]
      using prepBound.seq searchBound
  · constructor
    · intro hz hs; exact (iffhit.mpr hs) hz
    · intro hn; by_contra hz; exact hn (iffhit.mp hz)

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
