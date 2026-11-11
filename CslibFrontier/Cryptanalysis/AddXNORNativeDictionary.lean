/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeEmit

/-!
# Reusable sparse full-state dictionaries on the word RAM

A full state addresses three cells: a nonzero encoded first-quarter witness,
the second-quarter witness, and a link to the previous distinct state. Repeated
states replace their witness without adding a link. Releasing a class follows
these links and clears all three cells, rather than retaining old classes or
zeroing the entire state space. Empty memory outside the installed input is a
real prerequisite; arbitrary dirty dictionary cells are not silently admitted.

This is an original sparse-RAM implementation of the full-state dictionary
operation needed by [WangLvShenZhang2027], Theorem 7, PDF p. 22. It differs from
the source's sorted list. Address span is exponential in the state width;
occupied cells are counted separately. No multitape simulation, complete class
iterator, computed-balance composition or global dissection bound is claimed.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Dictionary

open Cslib.WordRAM
open Quarter

/-- Base of the sparse full-state slots. -/
abbrev table : Fin 32 := 27
/-- Top state plus one; zero denotes an empty dictionary. -/
abbrev top : Fin 32 := 28

/-- Address of a state's three-cell slot. -/
@[expose] def slot (D s : ℕ) : ℕ := D + 3 * s

/-- The exact memory effect of insertion, including the distinct-state link. -/
def putMemory (mem : ℕ → ℕ) (D t s u v : ℕ) : ℕ → ℕ :=
  let a := slot D s
  let linked := if mem a = 0 then Function.update mem (a + 2) t else mem
  Function.update (Function.update linked a (u + 1)) (a + 1) v

/-- Save a full-state record. Only a new state is pushed on the release chain.
The two witnesses are packed indices; adding one distinguishes index zero from
an absent entry. `state`, `operators` and `firstOperators` are preserved. -/
@[expose] def put : Code .standard 32 :=
  .seq (ram[ one ← #1; two ← #3; zero ← #0;
    address ← two * state; address ← table + address; operand ← *address ])
    (.seq (.branch (.eq operand zero)
      (ram[ bits ← address + one; bits ← bits + one; *bits ← top; top ← state + one ])
      (.op (.copy top top)))
      (ram[ operand ← firstOperators + one; *address ← operand;
        address ← address + one; *address ← operators ]))

/-- Exact insertion, including the conditional link allocation. No dictionary
oracle or compiler/runtime hypothesis is used. All non-scratch registers frame. -/
theorem put_exec {W D t s u v : ℕ} (x : Data 32)
    (hD : x.regs table = D) (ht : x.regs top = t) (hs : x.regs state = s)
    (hu : x.regs firstOperators = u) (hv : x.regs operators = v)
    (hfit : Fits W (D + 3 * s + s + u + 4)) :
    ∃ y, ExecWithin W put x y 16 ∧ y.mem = putMemory x.mem D t s u v ∧
      y.regs top = (if x.mem (slot D s) = 0 then s + 1 else t) ∧
      y.regs one = 1 ∧ y.regs zero = 0 := by
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have hmul : Fits W (3 * s) := hfit.of_le (by omega)
  have ha : Fits W (slot D s) := hfit.of_le (by dsimp [slot]; omega)
  let z := x.set one 1 |>.set two 3 |>.set zero 0 |>.set address (3 * s)
    |>.set address (slot D s) |>.set operand (x.mem (slot D s))
  have heSetup : ExecWithin (B := .standard) W
      (ram[ one ← #1; two ← #3; zero ← #0;
        address ← two * state; address ← table + address; operand ← *address ]) x z 6 := by
    dsimp only [slot] at ha
    ram_eval [z, hD, hs, h1, h3, hmul, ha, slot, one, two, zero,
      address, state, table, operand, Fin.mk.injEq]
  let linked := if x.mem (slot D s) = 0 then
    z.set bits (slot D s + 1) |>.set bits (slot D s + 2)
      |>.write (slot D s + 2) t |>.set top (s + 1)
    else z
  have heLink : ExecWithin W
      (.branch (.eq operand zero)
        (ram[ bits ← address + one; bits ← bits + one; *bits ← top; top ← state + one ])
        (.op (.copy top top))) z linked 6 := by
    by_cases hz : x.mem (slot D s) = 0
    · simp only [linked, hz, ↓reduceIte]
      apply (ExecWithin.branch_pos (T := 4) (cond := .eq operand zero)
        (by simp +decide [Cond.holds_eq, z, hz, operand, zero, address, one, two]) ?_).mono
        (by omega)
      have h2 : Fits W (slot D s + 2) := hfit.of_le (by dsimp [slot]; omega)
      have ha1 : Fits W (slot D s + 1) := h2.of_le (by omega)
      have hs1 : Fits W (s + 1) := hfit.of_le (by omega)
      dsimp only [slot] at ha1 h2
      simp only [Nat.add_assoc] at ha1 h2
      ram_eval [z, ht, hs, ha1, h2, hs1, slot, Nat.add_assoc, bits, address, one,
        top, state, operand, two, zero, Fin.mk.injEq]
    · simp only [linked, hz, ↓reduceIte]
      apply (ExecWithin.branch_neg (T := 1)
        (by simp +decide [Cond.holds_eq, z, hz, operand, zero, address, one, two]) ?_).mono
        (by omega)
      simpa [Data.set] using (ExecWithin.copy (w := W) (d := top) (s := top) (x := z))
  have frame (r : Fin 32) (hr : r ≠ bits ∧ r ≠ top ∧ r ≠ one ∧ r ≠ two ∧
      r ≠ zero ∧ r ≠ address ∧ r ≠ operand) : linked.regs r = x.regs r := by
    dsimp only [linked]
    split <;> simp [z, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
  have la : linked.regs address = slot D s := by
    dsimp only [linked]; split <;> simp +decide [z, address, bits, top, operand]
  have lo : linked.regs one = 1 := by
    dsimp only [linked]; split <;> simp +decide [z, one, bits, top, operand, address, zero, two]
  have lt : linked.regs top = (if x.mem (slot D s) = 0 then s + 1 else t) := by
    dsimp only [linked]; split <;> simp +decide [z, top, bits, operand, address, zero, one, two, ht]
  have lm : linked.mem = if x.mem (slot D s) = 0 then
      Function.update x.mem (slot D s + 2) t else x.mem := by
    dsimp only [linked]; split <;> rfl
  let y := linked.set operand (u + 1) |>.write (slot D s) (u + 1)
    |>.set address (slot D s + 1) |>.write (slot D s + 1) v
  have heOut : ExecWithin (B := .standard) W
      (ram[ operand ← firstOperators + one; *address ← operand;
        address ← address + one; *address ← operators ]) linked y 4 := by
    have huf : Fits W (u + 1) := hfit.of_le (by omega)
    have haf : Fits W (slot D s + 1) := hfit.of_le (by dsimp [slot]; omega)
    dsimp only [slot] at haf la
    ram_eval [y, la, lo, frame firstOperators (by decide), hu,
      frame operators (by decide), hv, huf, haf, operand, firstOperators, one,
      address, operators, Fin.mk.injEq]
  refine ⟨y, heSetup.seq (heLink.seq heOut), ?_, ?_, ?_, ?_⟩
  · simp only [y, Data.write_mem, Data.set_mem, lm, putMemory]
  · simpa +decide [y, top, address, operand] using lt
  · simpa +decide [y, one, address, operand] using lo
  · dsimp only [y, linked]
    split <;> simp +decide [z, zero, one, two, address, operand, bits, top]


/-- Read a full-state witness in six ordinary instructions. A nonzero tag is
one plus the first witness; the second witness is kept without encoding. -/
@[expose] def get : Code .standard 32 := ram[
  two ← #3; address ← two * state; address ← table + address;
  operand ← *address; address ← address + one; bits ← *address ]

/-- Exact direct-address lookup. It preserves all memory and the release stack.
Presence is the returned tag, not a test of either witness being nonzero. -/
theorem get_exec {W D s : ℕ} (x : Data 32) (hD : x.regs table = D)
    (hs : x.regs state = s) (ho : x.regs one = 1)
    (hfit : Fits W (D + 3 * s + 4)) :
    ∃ y, ExecWithin W get x y 6 ∧ y.mem = x.mem ∧
      y.regs operand = x.mem (slot D s) ∧ y.regs bits = x.mem (slot D s + 1) := by
  let y := x.set two 3 |>.set address (3 * s) |>.set address (slot D s)
    |>.set operand (x.mem (slot D s)) |>.set address (slot D s + 1)
    |>.set bits (x.mem (slot D s + 1))
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have hm : Fits W (3 * s) := hfit.of_le (by omega)
  have ha : Fits W (slot D s) := hfit.of_le (by dsimp [slot]; omega)
  have ha1 : Fits W (slot D s + 1) := hfit.of_le (by dsimp [slot]; omega)
  refine ⟨y, ?_, rfl, ?_, ?_⟩
  · dsimp only [slot] at ha ha1
    ram_eval [get, y, hD, hs, ho, h3, hm, ha, ha1, slot,
      two, address, state, table, operand, bits, one, Fin.mk.injEq]
  · simp +decide [y, operand, address, bits]
  · simp [y]

/-- Distinct full states have disjoint three-word slots. -/
theorem slot_ne {D s q i j : ℕ} (hs : s ≠ q) (hi : i < 3) (hj : j < 3) :
    slot D s + i ≠ slot D q + j := by dsimp [slot]; omega

/-- Insertion updates precisely the requested state's two witness cells. -/
theorem putMemory_read (mem : ℕ → ℕ) (D t s u v q : ℕ) :
    putMemory mem D t s u v (slot D q) =
        (if q = s then u + 1 else mem (slot D q)) ∧
      putMemory mem D t s u v (slot D q + 1) =
        (if q = s then v else mem (slot D q + 1)) := by
  by_cases h : q = s
  · subst q
    simp [putMemory]
  · have h0 := slot_ne (D := D) h (i := 0) (j := 0) (by omega) (by omega)
    have h1 := slot_ne (D := D) h (i := 0) (j := 1) (by omega) (by omega)
    have h2 := slot_ne (D := D) h (i := 0) (j := 2) (by omega) (by omega)
    have h10 := slot_ne (D := D) h (i := 1) (j := 0) (by omega) (by omega)
    have h11 := slot_ne (D := D) h (i := 1) (j := 1) (by omega) (by omega)
    have h12 := slot_ne (D := D) h (i := 1) (j := 2) (by omega) (by omega)
    simp only [Nat.add_zero] at h0 h1 h2 h10
    by_cases hz : mem (slot D s) = 0 <;>
      simp [putMemory, hz, h, h0, h1, h2, h10]

/-- The physical release chain stores state-plus-one links, not heap pointers. -/
inductive Chain (mem : ℕ → ℕ) (D : ℕ) : ℕ → List ℕ → Prop
  /-- Empty stack. -/
  | nil : Chain mem D 0 []
  /-- The last word of each occupied slot names the next distinct state. -/
  | cons {s t : ℕ} {ks : List ℕ} : mem (slot D s + 2) = t →
      Chain mem D t ks → Chain mem D (s + 1) (s :: ks)

/-- Only link cells are relevant to the release chain. -/
theorem Chain.frame {mem mem' : ℕ → ℕ} {D t : ℕ} {ks : List ℕ}
    (h : Chain mem D t ks) (hm : ∀ s ∈ ks, mem' (slot D s + 2) = mem (slot D s + 2)) :
    Chain mem' D t ks := by
  induction h with
  | nil => exact .nil
  | cons he ht ih =>
    exact .cons ((hm _ List.mem_cons_self).trans he)
      (ih (fun s hs => hm s (List.mem_cons_of_mem _ hs)))

/-- Memory after clearing exactly one occupied state. -/
def eraseMemory (mem : ℕ → ℕ) (D s : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update mem (slot D s + 2) 0)
    (slot D s) 0) (slot D s + 1) 0

/-- Erasure restores all three words, including the link. -/
theorem eraseMemory_read (mem : ℕ → ℕ) (D s i : ℕ) (hi : i < 3) :
    eraseMemory mem D s (slot D s + i) = 0 := by
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp [eraseMemory]

/-- Other states are untouched by erasure. -/
theorem eraseMemory_other (mem : ℕ → ℕ) (D s q i : ℕ) (hs : q ≠ s) (hi : i < 3) :
    eraseMemory mem D s (slot D q + i) = mem (slot D q + i) := by
  have h0 := slot_ne (D := D) hs hi (j := 0) (by omega)
  have h1 := slot_ne (D := D) hs hi (j := 1) (by omega)
  have h2 := slot_ne (D := D) hs hi (j := 2) (by omega)
  simp only [Nat.add_zero] at h0
  simp [eraseMemory, h0, h1, h2]

/-- Release one node, loading its successor before destroying its link. -/
@[expose] def pop : Code .standard 32 := ram[
  state ← top - one; address ← two * state; address ← table + address;
  bits ← address + one; bits ← bits + one; top ← *bits;
  *bits ← zero; *address ← zero; address ← address + one; *address ← zero ]

/-- Release the current class and return its sparse slots to zero. -/
@[expose] def release : Code .standard 32 :=
  .seq (ram[ one ← #1; two ← #3; zero ← #0 ]) (.loop (.lt zero top) pop)

/-- Exact memory observer of release; this list is proof data, not an input to
or an instruction of the release program. -/
def erasedMemory (mem : ℕ → ℕ) (D : ℕ) : List ℕ → ℕ → ℕ
  | [] => mem
  | s :: ks => erasedMemory (eraseMemory mem D s) D ks

/-- Native release follows the actual stored links. Distinctness guarantees
that clearing the head does not destroy a later link. -/
theorem releaseLoop_exec {W D t : ℕ} (ks : List ℕ) (x : Data 32)
    (hD : x.regs table = D) (ht : x.regs top = t)
    (ho : x.regs one = 1) (h3 : x.regs two = 3) (hz : x.regs zero = 0)
    (hc : Chain x.mem D t ks) (hn : ks.Nodup)
    (hfit : ∀ s ∈ ks, Fits W (D + 3 * s + 4)) :
    ∃ y, ExecWithin W (.loop (.lt zero top) pop) x y (12 * ks.length + 2) ∧
      y.mem = erasedMemory x.mem D ks ∧ y.regs top = 0 := by
  induction ks generalizing x t with
  | nil =>
    cases hc
    exact ⟨x, .loop_exit (by simp [Cond.holds_lt, hz, ht]), rfl, ht⟩
  | cons s ks ih =>
    cases hc with
    | cons he hc =>
      have hf := hfit s List.mem_cons_self
      have hm : Fits W (3 * s) := hf.of_le (by omega)
      have hs : Fits W s := hf.of_le (by omega)
      have ha : Fits W (slot D s) := hf.of_le (by dsimp [slot]; omega)
      have ha1 : Fits W (slot D s + 1) := hf.of_le (by dsimp [slot]; omega)
      have ha2 : Fits W (slot D s + 2) := hf.of_le (by dsimp [slot]; omega)
      let z := x.set state s |>.set address (3 * s) |>.set address (slot D s)
        |>.set bits (slot D s + 1) |>.set bits (slot D s + 2)
        |>.set top (x.mem (slot D s + 2))
        |>.write (slot D s + 2) 0 |>.write (slot D s) 0
        |>.set address (slot D s + 1) |>.write (slot D s + 1) 0
      have hePop : ExecWithin W pop x z 10 := by
        dsimp only [slot] at ha ha1 ha2
        simp only [Nat.add_assoc] at ha ha1 ha2
        ram_eval [pop, z, ht, ho, h3, hz, hm, hs, ha, ha1, ha2,
          slot, Nat.add_assoc, Nat.add_sub_cancel, state, top, one, two, address,
          table, bits, zero, Fin.mk.injEq, hD]
      have zm : z.mem = eraseMemory x.mem D s := rfl
      have frame (r : Fin 32) (hr : pop.Preserves r) : z.regs r = x.regs r :=
        hePop.regs_eq hr
      have zc : Chain z.mem D (x.mem (slot D s + 2)) ks := by
        rw [he]
        exact hc.frame (by
          intro q hq
          rw [zm, eraseMemory_other _ _ _ _ _ (by
            have := (List.nodup_cons.mp hn).1
            intro heq; subst q; contradiction) (by omega)])
      obtain ⟨y, hy, ym, yt⟩ := ih z ((frame table (by decide)).trans hD)
        (by simp +decide [z, top, address])
        ((frame one (by decide)).trans ho) ((frame two (by decide)).trans h3)
        ((frame zero (by decide)).trans hz) zc (List.nodup_cons.mp hn).2
        (fun q hq => hfit q (List.mem_cons_of_mem _ hq))
      refine ⟨y, ?_, ?_, yt⟩
      · exact (ExecWithin.loop_iter (by simp only [Cond.holds_lt, hz, ht]; omega)
          hePop hy).mono (by simp only [List.length_cons]; omega)
      · simpa only [erasedMemory, zm] using ym

/-- Full release includes setup and loop exit. Its cost depends on distinct
stored states, not on the exponentially large address span. -/
theorem release_exec {W D t : ℕ} (ks : List ℕ) (x : Data 32)
    (hD : x.regs table = D) (ht : x.regs top = t)
    (hc : Chain x.mem D t ks) (hn : ks.Nodup) (h1 : Fits W 3)
    (hfit : ∀ s ∈ ks, Fits W (D + 3 * s + 4)) :
    ∃ y, ExecWithin W release x y (12 * ks.length + 5) ∧
      y.mem = erasedMemory x.mem D ks ∧ y.regs top = 0 := by
  let z := x.set one 1 |>.set two 3 |>.set zero 0
  have he : ExecWithin (B := .standard) W (ram[ one ← #1; two ← #3; zero ← #0 ]) x z 3 := by
    ram_eval [z, h1, h1.of_le (by omega : 1 ≤ 3), one, two, zero, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yt⟩ := releaseLoop_exec ks z
    (by simpa +decide [z, table, one, two, zero] using hD)
    (by simpa +decide [z, top, one, two, zero] using ht)
    (by simp +decide [z, one, two, zero]) (by simp +decide [z, two, zero])
    (by simp [z]) hc hn hfit
  exact ⟨y, (he.seq hy).mono (by omega), ym, yt⟩

/-- Every occupied slot appears exactly once in the physical release stack.
Absent slots are completely zero, including their witness and link words. -/
structure Valid (mem : ℕ → ℕ) (D t : ℕ) (ks : List ℕ) : Prop where
  /-- Actual next links. -/
  chain : Chain mem D t ks
  /-- Duplicate states never allocate a second release entry. -/
  nodup : ks.Nodup
  /-- Tags identify precisely the occupied states. -/
  present : ∀ s, mem (slot D s) ≠ 0 ↔ s ∈ ks
  /-- No stale payload or link is hidden in an absent slot. -/
  absent : ∀ s, s ∉ ks → ∀ i < 3, mem (slot D s + i) = 0

/-- Empty memory above the installed input supplies the initial dictionary;
there is no exponential zero-fill hidden in this constructor. -/
theorem valid_empty {mem : ℕ → ℕ} {D : ℕ}
    (hz : ∀ s i, i < 3 → mem (slot D s + i) = 0) : Valid mem D 0 [] := by
  refine ⟨.nil, List.nodup_nil, ?_, ?_⟩
  · intro s
    have h := hz s 0 (by omega)
    simp only [Nat.add_zero] at h
    simp [h]
  · intro s _ i hi
    exact hz s i hi

/-- Link cells of existing states survive replacement of any two witness cells. -/
theorem putMemory_link (mem : ℕ → ℕ) (D t s u v q : ℕ)
    (hq : q ≠ s ∨ mem (slot D s) ≠ 0) :
    putMemory mem D t s u v (slot D q + 2) = mem (slot D q + 2) := by
  have h0 : slot D q + 2 ≠ slot D s := by dsimp [slot]; omega
  have h1 : slot D q + 2 ≠ slot D s + 1 := by dsimp [slot]; omega
  simp only [putMemory, Function.update_apply, h0, h1, ↓reduceIte]
  rcases hq with hq | hn
  · have h2 := slot_ne (D := D) hq (i := 2) (j := 2) (by omega) (by omega)
    by_cases hz : mem (slot D s) = 0 <;>
      simp only [hz, ↓reduceIte, Function.update_of_ne h2]
  · simp [hn]

/-- Every insertion maintains the release invariant, including collisions. -/
theorem Valid.put {mem : ℕ → ℕ} {D t : ℕ} {ks : List ℕ} (h : Valid mem D t ks)
    (s u v : ℕ) :
    Valid (putMemory mem D t s u v) D
      (if mem (slot D s) = 0 then s + 1 else t)
      (if mem (slot D s) = 0 then s :: ks else ks) := by
  have frame (q : ℕ) (hq : q ∈ ks) :
      putMemory mem D t s u v (slot D q + 2) = mem (slot D q + 2) := by
    apply putMemory_link
    by_cases heq : q = s
    · subst q
      exact Or.inr ((h.present s).mpr hq)
    · exact Or.inl heq
  have hp (q : ℕ) := (putMemory_read mem D t s u v q).1
  by_cases hz : mem (slot D s) = 0
  · have hs : s ∉ ks := fun hs => (h.present s).mpr hs hz
    simp only [hz, ↓reduceIte]
    refine ⟨.cons ?_ (h.chain.frame frame), List.nodup_cons.mpr ⟨hs, h.nodup⟩, ?_, ?_⟩
    · simp [putMemory, hz]
    · intro q
      rw [hp]
      by_cases hq : q = s <;> simp [hq, h.present]
    · intro q hq i hi
      have hqs : q ≠ s := fun heq => hq (List.mem_cons.mpr (Or.inl heq))
      have hqk : q ∉ ks := fun hmem => hq (List.mem_cons_of_mem _ hmem)
      have h0 := slot_ne (D := D) hqs hi (j := 0) (by omega)
      have h1 := slot_ne (D := D) hqs hi (j := 1) (by omega)
      have h2 := slot_ne (D := D) hqs hi (j := 2) (by omega)
      simp only [Nat.add_zero] at h0
      simp [putMemory, hz, h0, h1, h2, h.absent q hqk i hi]
  · simp only [hz, ↓reduceIte]
    refine ⟨h.chain.frame frame, h.nodup, ?_, ?_⟩
    · intro q
      rw [hp]
      by_cases hq : q = s
      · subst q
        simp [← h.present, hz]
      · simp [hq, h.present]
    · intro q hq i hi
      have hqs : q ≠ s := by intro he; subst q; exact hq ((h.present s).mp hz)
      have h0 := slot_ne (D := D) hqs hi (j := 0) (by omega)
      have h1 := slot_ne (D := D) hqs hi (j := 1) (by omega)
      simp only [Nat.add_zero] at h0
      simp [putMemory, hz, h0, h1, h.absent q hq i hi]

/-- Clearing never turns a zero cell into a nonzero cell. -/
theorem erasedMemory_zero {mem : ℕ → ℕ} {D a : ℕ} (ks : List ℕ) (ha : mem a = 0) :
    erasedMemory mem D ks a = 0 := by
  induction ks generalizing mem with
  | nil => exact ha
  | cons s ks ih =>
    apply ih
    simp only [eraseMemory, Function.update_apply]
    split_ifs <;> first | rfl | exact ha

/-- Every listed state's entire slot is zero after release. -/
theorem erasedMemory_read (mem : ℕ → ℕ) (D : ℕ) (ks : List ℕ)
    (s : ℕ) (hs : s ∈ ks) (i : ℕ) (hi : i < 3) :
    erasedMemory mem D ks (slot D s + i) = 0 := by
  induction ks generalizing mem with
  | nil => contradiction
  | cons q ks ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact erasedMemory_zero ks (eraseMemory_read mem D s i hi)
    · exact ih _ hs

/-- Release changes no cell outside the listed slots. -/
theorem erasedMemory_outside (mem : ℕ → ℕ) (D : ℕ) (ks : List ℕ) (a : ℕ)
    (ha : ∀ s ∈ ks, ∀ i < 3, a ≠ slot D s + i) : erasedMemory mem D ks a = mem a := by
  induction ks generalizing mem with
  | nil => rfl
  | cons s ks ih =>
    rw [erasedMemory, ih _ (fun q hq => ha q (List.mem_cons_of_mem _ hq))]
    have h0 := ha s List.mem_cons_self 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp [eraseMemory, h0, ha s List.mem_cons_self 1 (by omega),
      ha s List.mem_cons_self 2 (by omega)]

/-- Release restores an empty dictionary on every state, without scanning the
state space. The same sparse addresses may be used for the next class. -/
theorem Valid.release {mem : ℕ → ℕ} {D t : ℕ} {ks : List ℕ} (h : Valid mem D t ks) :
    Valid (erasedMemory mem D ks) D 0 [] := by
  apply valid_empty
  intro s i hi
  by_cases hs : s ∈ ks
  · exact erasedMemory_read mem D ks s hs i hi
  · exact erasedMemory_zero ks (h.absent s hs i hi)

/-- A physical full-state record and its two packed quarter witnesses. -/
structure Entry where
  /-- Complete state, never just its low bits. -/
  state : ℕ
  /-- First-quarter packed index. -/
  first : ℕ
  /-- Second-quarter packed index. -/
  second : ℕ
  deriving DecidableEq, Repr

/-- Exact final memory of successive insertions. -/
@[expose] def filledMemory (D : ℕ) : List Entry → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], mem, _ => mem
  | e :: es, mem, t => filledMemory D es
      (putMemory mem D t e.state e.first e.second)
      (if mem (slot D e.state) = 0 then e.state + 1 else t)

/-- Exact final release-stack register of successive insertions. -/
@[expose] def filledTop (D : ℕ) : List Entry → (ℕ → ℕ) → ℕ → ℕ
  | [], _, t => t
  | e :: es, mem, t => filledTop D es
      (putMemory mem D t e.state e.first e.second)
      (if mem (slot D e.state) = 0 then e.state + 1 else t)

/-- No insertion writes below the sparse-table base. -/
theorem putMemory_below (mem : ℕ → ℕ) (D t s u v a : ℕ) (ha : a < D) :
    putMemory mem D t s u v a = mem a := by
  have h0 : a ≠ slot D s := by dsimp [slot]; omega
  have h1 : a ≠ slot D s + 1 := by dsimp [slot]; omega
  have h2 : a ≠ slot D s + 2 := by dsimp [slot]; omega
  by_cases hz : mem (slot D s) = 0 <;> simp [putMemory, hz, h0, h1, h2]

/-- The native loader reads three words per input record. -/
@[expose] def fillBody : Code .standard 32 :=
  .seq (ram[ two ← #3; one ← #1; address ← two * position;
    address ← base + address; state ← *address; address ← address + one;
    firstOperators ← *address; address ← address + one; operators ← *address ])
    (.seq put (ram[ one ← #1; position ← position + one ]))

/-- Iterate over an actual physical input array, inserting every record. -/
@[expose] def fill : Code .standard 32 :=
  .seq (ram[ position ← #0 ]) (.loop (.lt position count) fillBody)

/-- Successive native insertions construct their own valid distinct-state stack;
the stack and its cardinality are conclusions, not caller-supplied certificates. -/
theorem filled_valid {mem : ℕ → ℕ} {D t : ℕ} {ks : List ℕ}
    (h : Valid mem D t ks) (es : List Entry) :
    ∃ keys, Valid (filledMemory D es mem t) D (filledTop D es mem t) keys ∧
      keys.length ≤ ks.length + es.length ∧
      ∀ s ∈ keys, s ∈ ks ∨ ∃ e ∈ es, e.state = s := by
  induction es generalizing mem t ks with
  | nil => exact ⟨ks, h, by simp, fun s hs => Or.inl hs⟩
  | cons e es ih =>
    obtain ⟨keys, hk, hl, hm⟩ := ih (h.put e.state e.first e.second)
    refine ⟨keys, hk, ?_, ?_⟩
    · split at hl <;> simp only [List.length_cons] at hl ⊢ <;> omega
    · intro q hq
      rcases hm q hq with hq | ⟨v, hv, he⟩
      · split at hq
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr ⟨e, List.mem_cons_self, rfl⟩
          · exact Or.inl hq
        · exact Or.inl hq
      · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

/-- Fill preserves every original input cell below the dictionary base. -/
theorem filledMemory_below (D : ℕ) (es : List Entry) (mem : ℕ → ℕ) (t a : ℕ)
    (ha : a < D) : filledMemory D es mem t a = mem a := by
  induction es generalizing mem t with
  | nil => rfl
  | cons e es ih => rw [filledMemory, ih, putMemory_below _ _ _ _ _ _ _ ha]

/-- Fill-loop correctness from the actual record cells. Original records must
end below the dictionary base. Every load, store, branch and iterator increment
is charged; records are not supplied to any machine instruction as host data. -/
theorem fillLoop_exec {W D b j t : ℕ} (es : List Entry) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = j + es.length)
    (hD : x.regs table = D) (ht : x.regs top = t) (hj : x.regs position = j)
    (hend : b + 3 * (j + es.length) ≤ D)
    (hinput : ∀ i (hi : i < es.length),
      x.mem (b + 3 * (j + i)) = es[i].state ∧
      x.mem (b + 3 * (j + i) + 1) = es[i].first ∧
      x.mem (b + 3 * (j + i) + 2) = es[i].second)
    (hfit : Fits W (D + j + es.length + 4))
    (hentries : ∀ e ∈ es, Fits W (D + 3 * e.state + e.state + e.first + 4)) :
    ∃ y, ExecWithin W (.loop (.lt position count) fillBody) x y (30 * es.length + 2) ∧
      y.mem = filledMemory D es x.mem t ∧ y.regs top = filledTop D es x.mem t := by
  induction es generalizing x j t with
  | nil =>
    exact ⟨x, .loop_exit (by simp [Cond.holds_lt, hj, hc]), rfl, ht⟩
  | cons e es ih =>
    obtain ⟨hstate, hfirst, hsecond⟩ := hinput 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hstate hfirst hsecond
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have h3 : Fits W 3 := hfit.of_le (by omega)
    have hm : Fits W (3 * j) := hfit.of_le (by simp only [List.length_cons] at hend; omega)
    have ha : Fits W (b + 3 * j) := hfit.of_le (by simp only [List.length_cons] at hend; omega)
    have ha1 : Fits W (b + 3 * j + 1) := hfit.of_le (by simp only [List.length_cons] at hend; omega)
    have ha2 : Fits W (b + 3 * j + 2) := hfit.of_le (by simp only [List.length_cons] at hend; omega)
    let z := x.set two 3 |>.set one 1 |>.set address (3 * j) |>.set address (b + 3 * j)
      |>.set state e.state |>.set address (b + 3 * j + 1) |>.set firstOperators e.first
      |>.set address (b + 3 * j + 2) |>.set operators e.second
    have heLoad : ExecWithin (B := .standard) W
        (ram[ two ← #3; one ← #1; address ← two * position;
          address ← base + address; state ← *address; address ← address + one;
          firstOperators ← *address; address ← address + one; operators ← *address ]) x z 9 := by
      simp only [Nat.add_assoc] at ha1 ha2 hfirst hsecond
      ram_eval [z, hb, hj, hstate, hfirst, hsecond, h1, h3, hm, ha, ha1, ha2,
        Nat.add_assoc, two, one, address, position, base, state, firstOperators, operators,
        Fin.mk.injEq]
    obtain ⟨u, hePut, um, ut, _, _⟩ := put_exec
      (D := D) (t := t) (s := e.state) (u := e.first) (v := e.second) z
      (by simpa +decide [z, table, two, one, address, state, firstOperators, operators] using hD)
      (by simpa +decide [z, top, two, one, address, state, firstOperators, operators] using ht)
      (by simp +decide [z, state, address, firstOperators, operators])
      (by simp +decide [z, firstOperators, address, operators]) (by simp [z])
      (hentries e List.mem_cons_self)
    have up : u.regs position = j := by
      rw [hePut.regs_eq (by decide)]
      simpa +decide [z, position, two, one, address, state, firstOperators, operators] using hj
    let next := (u.set one 1).set position (j + 1)
    have hj1 : Fits W (j + 1) := hfit.of_le (by simp only [List.length_cons]; omega)
    have heNext : ExecWithin (B := .standard) W
        (ram[ one ← #1; position ← position + one ]) u next 2 := by
      ram_eval [next, up, h1, hj1, one, position, Fin.mk.injEq]
    have heBody := heLoad.seq (hePut.seq heNext)
    have frame (r : Fin 32) (hr : fillBody.Preserves r) : next.regs r = x.regs r :=
      heBody.regs_eq hr
    have nm : next.mem = putMemory x.mem D t e.state e.first e.second := by
      simpa only [next, z, Data.set_mem] using um
    have nt : next.regs top = (if x.mem (slot D e.state) = 0 then e.state + 1 else t) := by
      change u.regs top = _
      exact ut
    have ninput : ∀ i (hi : i < es.length),
        next.mem (b + 3 * (j + 1 + i)) = es[i].state ∧
        next.mem (b + 3 * (j + 1 + i) + 1) = es[i].first ∧
        next.mem (b + 3 * (j + 1 + i) + 2) = es[i].second := by
      intro i hi
      have h := hinput (i + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at h
      have hbound : b + 3 * (j + (i + 1)) + 2 < D := by
        simp only [List.length_cons] at hend
        omega
      simp only [next, Data.set_mem, um, z, Data.set_mem]
      rw [putMemory_below _ _ _ _ _ _ _ (by omega),
        putMemory_below _ _ _ _ _ _ _ (by omega),
        putMemory_below _ _ _ _ _ _ _ (by omega)]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    obtain ⟨y, hy, ym, yt⟩ := ih next (j := j + 1)
      ((frame base (by decide)).trans hb)
      (by rw [frame count (by decide)]; simp only [List.length_cons] at hc; omega)
      ((frame table (by decide)).trans hD) nt (by simp [next])
      (by simp only [List.length_cons] at hend; omega) ninput
      (hfit.of_le (by simp only [List.length_cons]; omega))
      (fun e he => hentries e (List.mem_cons_of_mem _ he))
    · refine ⟨y, ?_, ?_, ?_⟩
      · exact (ExecWithin.loop_iter (by simp [Cond.holds_lt, hj, hc]) heBody hy).mono
          (by simp only [List.length_cons]; omega)
      · simpa only [filledMemory, nm] using ym
      · simpa only [filledTop, nm] using yt

/-- Native fill from an actual three-word record array. -/
theorem fill_exec {W D b t : ℕ} (es : List Entry) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = es.length)
    (hD : x.regs table = D) (ht : x.regs top = t)
    (hend : b + 3 * es.length ≤ D)
    (hinput : ∀ i (hi : i < es.length),
      x.mem (b + 3 * i) = es[i].state ∧ x.mem (b + 3 * i + 1) = es[i].first ∧
      x.mem (b + 3 * i + 2) = es[i].second)
    (hfit : Fits W (D + es.length + 4))
    (hentries : ∀ e ∈ es, Fits W (D + 3 * e.state + e.state + e.first + 4)) :
    ∃ y, ExecWithin W fill x y (30 * es.length + 3) ∧
      y.mem = filledMemory D es x.mem t ∧ y.regs top = filledTop D es x.mem t := by
  let z := x.set position 0
  obtain ⟨y, hy, ym, yt⟩ := fillLoop_exec es z (j := 0)
    (by simpa +decide [z, base, position] using hb)
    (by simpa +decide [z, count, position] using hc)
    (by simpa +decide [z, table, position] using hD)
    (by simpa +decide [z, top, position] using ht) (by simp [z])
    (by simpa only [Nat.zero_add] using hend)
    (by simpa only [z, Data.set_mem, Nat.zero_add] using hinput)
    (by simpa only [Nat.add_zero] using hfit) hentries
  have he : ExecWithin (B := .standard) W (ram[ position ← #0 ]) x z 1 :=
    ExecWithin.const (fits_zero _)
  exact ⟨y, (he.seq hy).mono (by omega), ym, yt⟩

/-- Witness cells after fill implement precisely last-writer replacement.
A zero tag means absence, even when both packed witnesses are zero. -/
theorem filledMemory_read (D : ℕ) (es : List Entry) (mem : ℕ → ℕ) (t q : ℕ) :
    (filledMemory D es mem t (slot D q), filledMemory D es mem t (slot D q + 1)) =
      es.foldl (fun old e => if q = e.state then (e.first + 1, e.second) else old)
        (mem (slot D q), mem (slot D q + 1)) := by
  induction es generalizing mem t with
  | nil => rfl
  | cons e es ih =>
    rw [filledMemory, ih, List.foldl_cons]
    obtain ⟨h0, h1⟩ := putMemory_read mem D t e.state e.first e.second q
    rw [h0, h1]
    split <;> rfl

/-- A present filled slot comes from an actual inserted record, including both
payload words from the same record. Only the queried initial tag must be empty;
collisions replace witnesses together and do not invent a witness. -/
theorem filledMemory_provenance (D : ℕ) (es : List Entry) (mem : ℕ → ℕ) (t q : ℕ)
    (hzero : mem (slot D q) = 0)
    (hit : filledMemory D es mem t (slot D q) ≠ 0) :
    ∃ e ∈ es, e.state = q ∧
      filledMemory D es mem t (slot D q) = e.first + 1 ∧
      filledMemory D es mem t (slot D q + 1) = e.second := by
  have trace (xs : List Entry) (old : ℕ × ℕ) :
      xs.foldl (fun prev e => if q = e.state then (e.first + 1, e.second) else prev) old =
        old ∨ ∃ e ∈ xs, e.state = q ∧
          xs.foldl (fun prev e => if q = e.state then (e.first + 1, e.second) else prev) old =
            (e.first + 1, e.second) := by
    induction xs generalizing old with
    | nil => exact Or.inl rfl
    | cons e xs ih =>
      rw [List.foldl_cons]
      obtain h | ⟨r, hr, hq, hv⟩ := ih (if q = e.state then (e.first + 1, e.second) else old)
      · by_cases hq : q = e.state
        · exact Or.inr ⟨e, List.mem_cons_self, hq.symm, by simpa only [hq, ↓reduceIte] using h⟩
        · exact Or.inl (by simpa only [hq, ↓reduceIte] using h)
      · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hq, hv⟩
  have read := filledMemory_read D es mem t q
  obtain h | ⟨e, he, hq, hv⟩ := trace es (mem (slot D q), mem (slot D q + 1))
  · have hz := congrArg Prod.fst (read.trans h)
    exact (hit (hz.trans hzero)).elim
  · have hp := read.trans hv
    exact ⟨e, he, hq, congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- All cells below the sparse table are unchanged by release. -/
theorem erasedMemory_below (mem : ℕ → ℕ) (D : ℕ) (ks : List ℕ) (a : ℕ)
    (ha : a < D) : erasedMemory mem D ks a = mem a := by
  apply erasedMemory_outside
  intro s _ i _
  dsimp [slot]
  omega

/-- Fill and release form one native lifetime. The next class reuses exactly
the same sparse slots after the release loop, not an ever-growing arena. -/
@[expose] def cycle : Code .standard 32 := .seq fill release

/-- Inserting a finite record stream into initially empty sparse slots produces
a valid release chain and restores the original memory when that chain is freed.
Only original input cells below `D` may be nonzero. -/
theorem filled_release {mem : ℕ → ℕ} {D : ℕ} (es : List Entry)
    (hzero : ∀ a, D ≤ a → mem a = 0) :
    ∃ keys, Valid (filledMemory D es mem 0) D (filledTop D es mem 0) keys ∧
      keys.length ≤ es.length ∧ (∀ q ∈ keys, ∃ e ∈ es, e.state = q) ∧
      erasedMemory (filledMemory D es mem 0) D keys = mem := by
  have hi : Valid mem D 0 [] := valid_empty (by
    intro s i _
    exact hzero _ (by dsimp [slot]; omega))
  obtain ⟨keys, hk, hl, hm⟩ := filled_valid hi es
  refine ⟨keys, hk, by simpa only [List.length_nil, Nat.zero_add] using hl, ?_, ?_⟩
  · intro q hq
    rcases hm q hq with hq | he
    · contradiction
    · exact he
  · funext a
    by_cases ha : a < D
    · rw [erasedMemory_below _ _ _ _ ha, filledMemory_below _ _ _ _ _ ha]
    · rw [hzero a (by omega)]
      have hv := hk.release.absent ((a - D) / 3) (by simp) ((a - D) % 3)
        (Nat.mod_lt _ (by omega))
      have hmod := Nat.mod_add_div (a - D) 3
      have heq : slot D ((a - D) / 3) + (a - D) % 3 = a := by dsimp [slot]; omega
      rwa [heq] at hv

/-- A complete native dictionary lifetime restores every original memory cell.
The support of the installed input must lie below `D`; this is stronger than
assuming tags are empty while silently allowing stale link/payload words. -/
theorem cycle_exec {W D b : ℕ} (es : List Entry) (x : Data 32)
    (hb : x.regs base = b) (hc : x.regs count = es.length)
    (hD : x.regs table = D) (ht : x.regs top = 0)
    (hend : b + 3 * es.length ≤ D)
    (hinput : ∀ i (hi : i < es.length),
      x.mem (b + 3 * i) = es[i].state ∧ x.mem (b + 3 * i + 1) = es[i].first ∧
      x.mem (b + 3 * i + 2) = es[i].second)
    (hzero : ∀ a, D ≤ a → x.mem a = 0)
    (hfit : Fits W (D + es.length + 4))
    (hentries : ∀ e ∈ es, Fits W (D + 3 * e.state + e.state + e.first + 4)) :
    ∃ y, ExecWithin W cycle x y (42 * es.length + 8) ∧ y.mem = x.mem ∧ y.regs top = 0 := by
  obtain ⟨z, hz, zm, zt⟩ := fill_exec es x hb hc hD ht hend hinput hfit hentries
  obtain ⟨keys, hk, hlen, hkeys, hrestore⟩ := filled_release es hzero
  have zk : Valid z.mem D (z.regs top) keys := by rwa [zm, zt]
  obtain ⟨y, hy, ym, yt⟩ := release_exec keys z
    ((hz.regs_eq (by decide)).trans hD) rfl zk.chain zk.nodup (hfit.of_le (by omega))
    (by
      intro q hq
      obtain ⟨e, he, rfl⟩ := hkeys q hq
      exact (hentries e he).of_le (by omega))
  refine ⟨y, (hz.seq hy).mono (by omega), ?_, yt⟩
  rw [ym, zm]
  exact hrestore

/-- Through-halt instruction and simultaneous prefix-support certificate for a
complete lifetime. The record count bounds each lifetime independently; no sum
of previous class sizes appears. This does not include a streamed probe phase
or infer that these records are the counter-selected smaller class. -/
theorem cycle_resources {W D b : ℕ} (es : List Entry) (x : Data 32) (S : Finset ℕ)
    (hx : x.Bounded W) (hS : ∀ a, x.mem a ≠ 0 → a ∈ S)
    (hb : x.regs base = b) (hc : x.regs count = es.length)
    (hD : x.regs table = D) (ht : x.regs top = 0)
    (hend : b + 3 * es.length ≤ D)
    (hinput : ∀ i (hi : i < es.length),
      x.mem (b + 3 * i) = es[i].state ∧ x.mem (b + 3 * i + 1) = es[i].first ∧
      x.mem (b + 3 * i + 2) = es[i].second)
    (hzero : ∀ a, D ≤ a → x.mem a = 0)
    (hfit : Fits W (D + es.length + 4))
    (hentries : ∀ e ∈ es, Fits W (D + 3 * e.state + e.state + e.first + 4)) :
    ∃ y n ts, n + 1 ≤ 42 * es.length + 9 ∧ TraceExec W cycle x y n ts ∧
      Executes W (cycle.program top) ⟨0, x⟩ 0 (n + 1) ∧ y.mem = x.mem ∧
      ∀ k u, Runs W (cycle.program top) ⟨0, x⟩ u k → k ≤ n →
        u.data.Bounded W ∧ ∃ live : Finset ℕ,
          (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
          (live.card + 32) * W ≤ (S.card + 42 * es.length + 40) * W := by
  obtain ⟨y, ⟨n, hn, he⟩, hm, ht⟩ := cycle_exec es x hb hc hD ht hend hinput hzero hfit hentries
  obtain ⟨ts, heTrace⟩ := he.exists_trace
  refine ⟨y, n, ts, by omega, heTrace, ?_, hm, ?_⟩
  · simpa only [ht] using he.executes top
  · intro k u hu hk
    obtain ⟨cover, hcard, hcover⟩ := hu.exists_memorySupport S hS
    refine ⟨hu.bounded hx, cover.filter (fun a => u.data.mem a ≠ 0), ?_, ?_⟩
    · intro a
      simp only [Finset.mem_filter]
      exact ⟨fun ha => ⟨hcover a ha, ha⟩, And.right⟩
    · apply Nat.mul_le_mul_right
      have := Finset.card_filter_le cover (fun a => u.data.mem a ≠ 0)
      omega

end Cslib.Cryptanalysis.AddXNOR.Native.Dictionary
