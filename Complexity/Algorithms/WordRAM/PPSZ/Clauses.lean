/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PPZ.Forced
public import Complexity.Algorithms.WordRAM.PPSZ.Odometer
public import Complexity.Computability.Complexity.FineGrained.PPSZ.Search
import Mathlib.Data.Nat.Bitwise

/-!
# The w-implication search on stored clauses

The word-RAM program `Cslib.Algorithms.WordRAM.PPSZ.impliedCode` decides w-implication
(`Cslib.Complexity.PPSZ.WImplied`) by the finite search `Cslib.Complexity.PPSZ.impliedTest`, run on
addresses instead of clauses and literals. A choice of clauses is a list of the addresses where
their encodings start (`Cslib.Algorithms.WordRAM.PPSZ.clauseAddrs`), and a choice of literals is a
list of the addresses of their codes in those encodings. This file states that search on stored
data (`Cslib.Algorithms.WordRAM.PPSZ.addrTest`) and proves that it is `impliedTest`
(`Cslib.Algorithms.WordRAM.PPSZ.addrTest_eq`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.clauseAddrs`, `Cslib.Algorithms.WordRAM.PPSZ.clauseOf`: where the
  encodings of the clauses start, and the clause stored at an address.
* `Cslib.Algorithms.WordRAM.PPSZ.litFine`, `Cslib.Algorithms.WordRAM.PPSZ.compatCodes`: the
  compatibility test on literal codes.
* `Cslib.Algorithms.WordRAM.PPSZ.addrTest`: the search on stored data.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.succIn_clauseAddrs`, `Cslib.Algorithms.WordRAM.PPSZ.succIn_range'`:
  the odometer steps of the two searches.
* `Cslib.Algorithms.WordRAM.PPSZ.compatCodes_map_litCode`: compatibility through codes.
* `Cslib.Algorithms.WordRAM.PPSZ.addrTest_eq`: the search on stored data is `impliedTest`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

open Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPSZ
open Cslib.Algorithms.WordRAM.Schoening (litCode encodeClause encodeClauses encodeClauses_cons
  encodeClauses_nil length_encodeClause litCode_shiftRight litCode_and_one)
open Cslib.Algorithms.WordRAM.PPZ (optCode PartialAt)

variable {n : ℕ}

/-! ### Sections under maps -/

/-- Sections commute with mapping every entry. -/
theorem sections_map_map {α β : Type*} (f : α → β) :
    ∀ L : List (List α), (L.map (List.map f)).sections = L.sections.map (List.map f)
  | [] => rfl
  | l :: L => by
    simp only [List.map_cons, List.sections, sections_map_map f L, List.flatMap_map,
      List.map_flatMap, List.map_map]
    rfl

/-- `List.any` depends only on the values of the test on the list. -/
theorem any_congr_of_mem {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

/-! ### Clause addresses -/

/-- The addresses where the encodings of the clauses of `φ` start, when the encoding of `φ` starts
at address `a`. -/
def clauseAddrs : ℕ → CNF (Fin n) → List ℕ
  | _, [] => []
  | a, c :: φ => a :: clauseAddrs (a + 1 + c.length) φ

/-- The clause of `φ` whose encoding starts at address `p`, when the encoding of `φ` starts at
address `a` (the empty clause at other addresses). -/
def clauseOf : ℕ → CNF (Fin n) → ℕ → Clause (Fin n)
  | _, [], _ => []
  | a, c :: φ, p => if p = a then c else clauseOf (a + 1 + c.length) φ p

/-- Clause addresses lie in the encoding, with their clause. -/
theorem bounds_of_mem_clauseAddrs :
    ∀ {a : ℕ} {φ : CNF (Fin n)} {p : ℕ}, p ∈ clauseAddrs a φ →
      a ≤ p ∧ p + 1 + (clauseOf a φ p).length ≤ a + (encodeClauses φ).length
  | _, [], _, h => by simp [clauseAddrs] at h
  | a, c :: φ, p, h => by
    simp only [clauseAddrs, List.mem_cons] at h
    rcases h with rfl | h
    · simp [clauseOf]; omega
    · obtain ⟨h1, h2⟩ := bounds_of_mem_clauseAddrs h
      have hp : p ≠ a := by omega
      simp only [clauseOf, hp, ↓reduceIte, encodeClauses_cons, List.length_append,
        length_encodeClause]
      omega

/-- The clauses at the clause addresses are the clauses of `φ`. -/
theorem map_clauseOf_clauseAddrs :
    ∀ (a : ℕ) (φ : CNF (Fin n)), (clauseAddrs a φ).map (clauseOf a φ) = φ
  | _, [] => rfl
  | a, c :: φ => by
    simp only [clauseAddrs, List.map_cons, clauseOf, ↓reduceIte, List.cons.injEq, true_and]
    refine (List.map_congr_left fun p hp => ?_).trans (map_clauseOf_clauseAddrs _ φ)
    have := (bounds_of_mem_clauseAddrs hp).1
    simp only [show p ≠ a by omega, ↓reduceIte]

/-- Clause addresses are duplicate-free. -/
theorem clauseAddrs_nodup : ∀ (a : ℕ) (φ : CNF (Fin n)), (clauseAddrs a φ).Nodup
  | _, [] => List.nodup_nil
  | a, c :: φ => List.nodup_cons.mpr
      ⟨fun h => by have := (bounds_of_mem_clauseAddrs h).1; omega, clauseAddrs_nodup _ φ⟩

/-- The encoding of the clause stored at a clause address. -/
theorem holdsList_clauseOf {mem : ℕ → ℕ} :
    ∀ {a : ℕ} {φ : CNF (Fin n)}, HoldsList a (encodeClauses φ) mem → ∀ {p : ℕ},
      p ∈ clauseAddrs a φ → HoldsList p (encodeClause (clauseOf a φ p)) mem
  | _, [], _, _, h => by simp [clauseAddrs] at h
  | a, c :: φ, hφ, p, h => by
    rw [encodeClauses_cons] at hφ
    obtain ⟨hc, hrest⟩ := holdsList_append_iff.mp hφ
    simp only [clauseAddrs, List.mem_cons] at h
    rcases h with rfl | h
    · simpa [clauseOf] using hc
    · have := (bounds_of_mem_clauseAddrs h).1
      simp only [clauseOf, show p ≠ a by omega, ↓reduceIte]
      rw [length_encodeClause, show a + (c.length + 1) = a + 1 + c.length by omega] at hrest
      exact holdsList_clauseOf hrest h

/-- The length word of the clause stored at a clause address. -/
theorem mem_clauseAddr {mem : ℕ → ℕ} {a : ℕ} {φ : CNF (Fin n)}
    (hφ : HoldsList a (encodeClauses φ) mem) {p : ℕ} (hp : p ∈ clauseAddrs a φ) :
    mem p = (clauseOf a φ p).length := by
  simpa [encodeClause] using (holdsList_clauseOf hφ hp).get 0 (by simp)

/-- The codes of the literals of the clause stored at a clause address. -/
theorem map_range'_clauseOf {mem : ℕ → ℕ} {a : ℕ} {φ : CNF (Fin n)}
    (hφ : HoldsList a (encodeClauses φ) mem) {p : ℕ} (hp : p ∈ clauseAddrs a φ) :
    (List.range' (p + 1) (mem p)).map mem = (clauseOf a φ p).map litCode := by
  have hc := holdsList_clauseOf hφ hp
  rw [mem_clauseAddr hφ hp]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range']
  have := hc.get (i + 1) (by simp at h2 ⊢; omega)
  simpa [encodeClause, Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **The odometer step of a clause address**: the next clause starts after the length word and
the literals; after the last clause comes the end of the encoding. -/
theorem succIn_clauseAddrs :
    ∀ {a : ℕ} {φ : CNF (Fin n)} {p : ℕ}, p ∈ clauseAddrs a φ →
      succIn (clauseAddrs a φ) p =
        if p + 1 + (clauseOf a φ p).length = a + (encodeClauses φ).length then none
        else some (p + 1 + (clauseOf a φ p).length)
  | _, [], _, h => by simp [clauseAddrs] at h
  | a, c :: φ, p, h => by
    simp only [clauseAddrs, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [clauseAddrs, succIn, ↓reduceIte, clauseOf, encodeClauses_cons,
        List.length_append, length_encodeClause]
      rcases φ with _ | ⟨c', φ⟩
      · simp [clauseAddrs]; omega
      · simp only [clauseAddrs, List.head?_cons, encodeClauses_cons, List.length_append,
          length_encodeClause]
        split_ifs with h
        · omega
        · rfl
    · have hb := bounds_of_mem_clauseAddrs h
      simp only [clauseAddrs, succIn, show p ≠ a by omega, ↓reduceIte, clauseOf,
        encodeClauses_cons, List.length_append, length_encodeClause]
      rw [succIn_clauseAddrs h, show a + (c.length + 1 + (encodeClauses φ).length) =
        a + 1 + c.length + (encodeClauses φ).length by omega]

/-- The first clause address is the start of the encoding. -/
theorem headD_clauseAddrs {a : ℕ} {φ : CNF (Fin n)} (hφ : φ ≠ []) (d : ℕ) :
    (clauseAddrs a φ).headD d = a := by
  rcases φ with _ | ⟨c, φ⟩
  · exact absurd rfl hφ
  · rfl

/-- **The odometer step of a literal address**: the next address, up to the end of the clause. -/
theorem succIn_range' {s k e : ℕ} (he : e ∈ List.range' s k) :
    succIn (List.range' s k) e = if e + 1 = s + k then none else some (e + 1) := by
  induction k generalizing s with
  | zero => simp at he
  | succ k ih =>
    rw [List.range'_succ]
    rw [List.range'_succ, List.mem_cons] at he
    rcases he with rfl | he
    · rcases k with _ | k
      · simp [succIn]
      · simp [succIn, List.range'_succ]
    · have hs : e ≠ s := by rw [List.mem_range'_1] at he; omega
      simp only [succIn, hs, ↓reduceIte]
      rw [ih he, show s + 1 + k = s + (k + 1) by omega]

/-! ### Compatibility through codes -/

/-- Whether the literal with code `c` is not falsified when the partial assignment stored as the
words `tw v` is changed to set the variable `x` to `!b`, where `b` is `0` or `1`. -/
def litFine (tw : ℕ → ℕ) (x b c : ℕ) : Bool :=
  if c >>> 1 = x then (c &&& 1) != b else tw (c >>> 1) != 1 - (c &&& 1)

/-- **Compatibility through codes**: no literal is falsified, and no code is the code of the
complement `c ^^^ 1` of another. -/
def compatCodes (tw : ℕ → ℕ) (x b : ℕ) (cs : List ℕ) : Bool :=
  cs.all fun c => litFine tw x b c && cs.all fun c' => c' != c ^^^ 1

/-- The code of the complementary literal. -/
theorem litCode_xor_one (l : Literal (Fin n)) : litCode l ^^^ 1 = litCode (l.1, !l.2) := by
  obtain ⟨v, b⟩ := l
  simp only [litCode]
  cases b
  · simp only [Bool.toNat_false, Nat.add_zero, Bool.not_false, Bool.toNat_true]
    exact Nat.xor_one_of_even (even_two_mul _)
  · simp only [Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero]
    rw [Nat.xor_one_of_odd (odd_two_mul_add_one _)]
    omega

/-- Literal codes determine literals. -/
theorem litCode_injective : Function.Injective (litCode (n := n)) := by
  intro l l' h
  have h1 := congrArg (· >>> 1) h
  have h2 := congrArg (· &&& 1) h
  simp only [litCode_shiftRight, litCode_and_one] at h1 h2
  exact Prod.ext (Fin.ext h1) (by cases hl : l.2 <;> cases hl' : l'.2 <;> simp_all)

/-- The word of a stored value is `1 - s` exactly when the value is `!s`. -/
theorem optCode_eq_one_sub_iff (o : Option Bool) (s : Bool) :
    optCode o = 1 - s.toNat ↔ o = some (!s) := by
  rcases o with _ | a
  · cases s <;> simp [optCode]
  · cases a <;> cases s <;> simp [optCode]

/-- **Compatibility through codes** is compatibility of the literals, with `x` set to `!b`. -/
theorem compatCodes_map_litCode {mem : ℕ → ℕ} {Tb : ℕ} {τ : Fin n → Option Bool}
    (hτ : PartialAt mem Tb τ) (x : Fin n) (b : Bool) (ls : List (Literal (Fin n))) :
    compatCodes (fun v => mem (Tb + v)) x b.toNat (ls.map litCode) =
      compatible (Function.update τ x (some !b)) ls := by
  have hfine : ∀ l : Literal (Fin n), litFine (fun v => mem (Tb + v)) x b.toNat (litCode l) =
      (Function.update τ x (some !b) l.1 != some (!l.2)) := by
    intro l
    simp only [litFine, litCode_shiftRight, litCode_and_one]
    by_cases hlx : l.1 = x
    · subst hlx
      simp only [↓reduceIte, Function.update_self]
      cases l.2 <;> cases b <;> rfl
    · have hv : l.1.val ≠ x.val := fun h => hlx (Fin.ext h)
      simp only [hv, ↓reduceIte, Function.update_of_ne hlx, hτ l.1]
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq, optCode_eq_one_sub_iff]
  have hpair : ∀ l l' : Literal (Fin n), (litCode l' != litCode l ^^^ 1) = (l' != (l.1, !l.2)) := by
    intro l l'
    rw [litCode_xor_one, Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq]
    exact not_congr litCode_injective.eq_iff
  simp only [compatCodes, compatible, List.all_map, Function.comp_def, hfine, hpair]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun l hl => (h l hl).1, fun l hl => (h l hl).2⟩,
    fun h l hl => ⟨h.1 l hl, h.2 l hl⟩⟩

/-! ### The search on stored data -/

/-- **The w-implication search on stored data**: the clauses of `φ` are stored from address `C`,
and the words of a partial assignment from `Tb`. The search accepts if the word of `x` is `b`, or
some choice of `s` clause addresses has no compatible choice of literal addresses. -/
def addrTest (mem : ℕ → ℕ) (C Tb : ℕ) (φ : CNF (Fin n)) (s x b : ℕ) : Bool :=
  mem (Tb + x) == b || (List.replicate s (clauseAddrs C φ)).sections.any fun D =>
    !(D.map fun p => List.range' (p + 1) (mem p)).sections.any fun E =>
      compatCodes (fun v => mem (Tb + v)) x b (E.map mem)

/-- The word of a stored value is `b` exactly when the value is `b`. -/
theorem optCode_eq_toNat_iff (o : Option Bool) (b : Bool) : optCode o = b.toNat ↔ o = some b := by
  rcases o with _ | a
  · cases b <;> simp [optCode]
  · cases a <;> cases b <;> simp [optCode]

/-- **The search on stored data is the w-implication search** `Cslib.Complexity.PPSZ.impliedTest`,
when the clauses of `φ` are stored from `C` and the partial assignment `τ` from `Tb`. -/
theorem addrTest_eq {mem : ℕ → ℕ} {C Tb : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (hφ : HoldsList C (encodeClauses φ) mem) (hτ : PartialAt mem Tb τ) (s : ℕ) (x : Fin n)
    (b : Bool) : addrTest mem C Tb φ s x b.toNat = impliedTest φ s τ x b := by
  have hinner : ∀ D ∈ (List.replicate s (clauseAddrs C φ)).sections,
      ((D.map fun p => List.range' (p + 1) (mem p)).sections.any fun E =>
        compatCodes (fun v => mem (Tb + v)) x b.toNat (E.map mem)) =
      (D.map (clauseOf C φ)).sections.any (compatible (Function.update τ x (some !b))) := by
    intro D hD
    have hD' := (mem_sections_replicate.mp hD).2
    have hmap : (D.map fun p => List.range' (p + 1) (mem p)).map (List.map mem) =
        (D.map (clauseOf C φ)).map (List.map litCode) := by
      simp only [List.map_map]
      exact List.map_congr_left fun p hp => by
        simp only [Function.comp_apply]
        exact map_range'_clauseOf hφ (hD' p hp)
    have h1 := congrArg
      (fun L => (List.sections L).any (compatCodes (fun v => mem (Tb + v)) x b.toNat)) hmap
    simp only [sections_map_map, List.any_map, Function.comp_def] at h1
    rw [h1]
    exact any_congr_of_mem fun ls _ => compatCodes_map_litCode hτ x b ls
  have houter : (List.replicate s (clauseAddrs C φ)).sections.map (List.map (clauseOf C φ)) =
      (List.replicate s φ).sections := by
    rw [← sections_map_map, List.map_replicate, map_clauseOf_clauseAddrs]
  unfold addrTest impliedTest
  congr 1
  · rw [hτ x, Bool.eq_iff_iff]
    simp only [beq_iff_eq, optCode_eq_toNat_iff]
  · rw [← houter, List.any_map]
    exact any_congr_of_mem fun D hD => by rw [hinner D hD]; rfl

end Cslib.Algorithms.WordRAM.PPSZ
