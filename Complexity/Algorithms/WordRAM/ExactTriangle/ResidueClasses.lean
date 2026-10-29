/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Classes
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
public import Complexity.Computability.WordRAM.Compile
public import Mathlib.Data.List.GetD

/-!
# Initialized signed weights to native residue classes

The flat input is an unsigned `(n,p)` header followed by the signed encodings of the three
`n×n` weight matrices. Native arithmetic allocates a residue array, class counts and disjoint
query blocks. The existing signed residue kernel processes every weight before the class scanner
reads the A–B residues. Neither residues nor class/layout tables are input certificates.

## Main definitions

* `ResidueClasses.input`: the mixed unsigned-header/signed-weight encoding.
* `ResidueClasses.programAt`: the same preparation at a fixed caller header offset.
* `ResidueClasses.program`: fixed thirty-two-register native preparation.
* `ResidueClasses.addressBound`: explicit arithmetic and allocation bound.

## Main results

* `ResidueClasses.exec_at`: callable execution from a fixed caller header.
* `ResidueClasses.exec_input`: initialized execution, residues, class counts, queries and frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ResidueClasses

open Cslib.WordRAM

open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

/-- Header cursor and class-scanner source register. -/
abbrev temp : Fin 32 := 0
/-- Class-scanner side register. -/
abbrev scanSize : Fin 32 := 2
/-- Signed-residue source register. -/
abbrev weightSrc : Fin 32 := 9
/-- Signed-residue destination register. -/
abbrev weightDst : Fin 32 := 10
/-- Signed-residue length register. -/
abbrev weightLen : Fin 32 := 11
/-- Signed modulus and subsequent class-count pointer register. -/
abbrev encodedMod : Fin 32 := 12
/-- Class-scanner query pointer register. -/
abbrev scanQueries : Fin 32 := 13
/-- Class-scanner modulus register. -/
abbrev scanModulus : Fin 32 := 14

/-- Unsigned side length. -/
abbrev size : Fin 32 := 24
/-- Unsigned positive modulus. -/
abbrev modulus : Fin 32 := 25
/-- Start of the signed weights. -/
abbrev weights : Fin 32 := 26
/-- Start of all three unsigned residue matrices. -/
abbrev residues : Fin 32 := 27
/-- Start of the computed class-count array. -/
abbrev counts : Fin 32 := 28
/-- Start of the class query blocks. -/
abbrev queries : Fin 32 := 29
/-- Area of one weight matrix. -/
abbrev area : Fin 32 := 30
/-- Constant one, preserved by both callees. -/
abbrev one : Fin 32 := 31

/-- Header followed by the three signed weight matrices in A–B, B–C, A–C order. -/
def input (n p : ℕ) (values : List ℤ) : List ℕ := [n, p] ++ values.map Signed.encode

/-- A fitting value covering every allocation endpoint and temporary for a caller header.
The adjacent header cells contain `n,p`, followed by the three signed matrices. -/
def addressBoundAt (header n p : ℕ) : ℕ :=
  header + 2 + 6 * (n * n) + p + 2 * (n * n) * p + 4

/-- The standard input places its `n,p` header immediately after the machine's length cell. -/
def addressBound (n p : ℕ) : ℕ := addressBoundAt 1 n p

private abbrev bank (r : ℕ) (hr : r ≤ 24) : Fin r → Fin 32 := Fin.castLE (by omega)

private theorem bank_injective (r : ℕ) (hr : r ≤ 24) : (bank r hr).Injective := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

/-- The existing signed residue conversion, including unsigned decoding of each remainder. -/
def reduce : Code .standard 32 := Residues.program.rename (Fin.castLE (by decide))

/-- Reuse the complete native class scanner. -/
def classify : Code .standard 32 := Classes.program.rename (Fin.castLE (by decide))

/-- Read a fixed caller header and compute all array bases, lengths and the encoded modulus.
The offset is a code parameter; the complete ET caller uses one fixed input format. -/
def setupAt (header : ℕ) : Code .standard 32 := ram[
  one ← #1; temp ← #header; size ← *temp; temp ← temp + one; modulus ← *temp;
  weights ← #(header + 2); area ← size * size; weightLen ← area + area;
  weightLen ← weightLen + area;
  weightSrc ← weights; weightDst ← weights + weightLen; residues ← weightDst;
  counts ← residues + weightLen; queries ← counts + modulus; encodedMod ← modulus + modulus ]

/-- Read the standard initialized input header. -/
def setup : Code .standard 32 := setupAt 1

/-- Deliver the five actual scanner arguments after residue conversion. -/
def deliver : Code .standard 32 := ram[
  temp ← residues; scanSize ← size; encodedMod ← counts;
  scanQueries ← queries; scanModulus ← modulus ]

/-- Native setup, reduction and enumeration for a fixed caller header. -/
def programAt (header : ℕ) : Code .standard 32 :=
  .seq (setupAt header) (.seq reduce (.seq deliver classify))

/-- All setup, reduction and enumeration is native code. -/
def program : Code .standard 32 := programAt 1

/-- Changing the fixed header offset changes constants but not the instruction graph. -/
theorem programAt_fixed (header : ℕ) :
    (programAt header).size ≤ 160 ∧ ¬(programAt header).ReadsWidth := by
  change (programAt 0).size ≤ 160 ∧ ¬(programAt 0).ReadsWidth
  decide

/-- Fixed instruction graph, independent of dimensions and physical width. -/
theorem program_fixed : program.size ≤ 160 ∧ ¬program.ReadsWidth := by decide

private theorem reduce_preserves : ∀ i : Fin 32, 24 ≤ i.val → reduce.Preserves i := by decide

private theorem classify_preserves : ∀ i : Fin 32, 24 ≤ i.val → classify.Preserves i := by decide

private theorem input_weight (n p : ℕ) (values : List ℤ) (q : ℕ) :
    (Data.init (input n p values) : Data 32).mem (3 + q) = Signed.encode (values.getD q 0) := by
  rw [show 3 + q = (q + 2) + 1 by omega, Data.init_mem_succ]
  simp only [input, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.cons_append, List.nil_append, List.getElem?_map]
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_map,
    Signed.encode, Int.natAbs_zero, lt_self_iff_false,
    ↓reduceIte, Nat.mul_zero, Nat.add_zero] using (List.getD_map values (n := q) Signed.encode
      (d := (0 : ℤ)))

/-- Callable residue/class preparation from a concrete caller header and signed matrix words.
The fixed offset selects the adjacent `n,p` cells; no initialized-memory shape is assumed outside
that payload. The cost and output frame include every setup, signed reduction and class scan. -/
theorem exec_at {w : ℕ} (header n p : ℕ) (values : ℕ → ℤ) (initial : Data 32)
    (hnHeader : initial.mem header = n) (hpHeader : initial.mem (header + 1) = p)
    (hinput : ∀ q < 3 * (n * n),
      initial.mem (header + 2 + q) = Signed.encode (values q))
    (hp : 0 < p) (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (haddress : Fits (w + 2) (addressBoundAt header n p)) :
    let base := header + 2
    ∃ y, ExecWithin (w + 2) (programAt header) initial y
        (69 * (n * n) + p * (14 * (n * n) + 14) + 30) ∧
      y.regs residues = base + 3 * (n * n) ∧ y.regs counts = base + 6 * (n * n) ∧
      y.regs queries = base + 6 * (n * n) + p ∧
      (∀ q < 3 * (n * n), y.mem (base + 3 * (n * n) + q) =
        (values q % (p : ℤ)).toNat) ∧
      (∀ j < p, y.mem (base + 6 * (n * n) + j) =
        Nat.count (fun q => (values q % (p : ℤ)).toNat = j) (n * n)) ∧
      (∀ j < p, ∀ q < n * n, (values q % (p : ℤ)).toNat = j →
        y.mem (base + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values k % (p : ℤ)).toNat = j) q) = q / n ∧
        y.mem (base + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values k % (p : ℤ)).toNat = j) q + 1) = q % n) ∧
      (∀ a, a < base + 3 * (n * n) ∨
        base + 6 * (n * n) + p + 2 * (n * n) * p ≤ a →
          y.mem a = initial.mem a) := by
  let N := n * n
  let base := header + 2
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  have h1 : Fits (w + 2) 1 := haddress.of_le (by simp only [addressBoundAt]; omega)
  have hhead : Fits (w + 2) header := haddress.of_le
    (by simp only [addressBoundAt]; omega)
  have hhead1 : Fits (w + 2) (header + 1) := haddress.of_le
    (by simp only [addressBoundAt]; omega)
  have hbase : Fits (w + 2) base := haddress.of_le
    (by simp only [addressBoundAt]; dsimp only [base]; omega)
  have hN : Fits (w + 2) N := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have h2N : Fits (w + 2) (N + N) := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have h3N : Fits (w + 2) (N + N + N) := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have hres : Fits (w + 2) (base + (N + N + N)) := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have hcounts : Fits (w + 2) (base + (N + N + N) + (N + N + N)) := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have hqueries : Fits (w + 2) (base + (N + N + N) + (N + N + N) + p) := haddress.of_le
    (by simp only [addressBoundAt]; dsimp [N, base]; omega)
  have hmodfit : Fits (w + 2) (p + p) := by
    have h := (Signed.encode_fits hmod).mono (show w + 1 ≤ w + 2 by omega)
    simpa [Signed.encode, two_mul, show ¬(p : ℤ) < 0 by omega] using h
  have hsizeFit : Fits (w + 2) n := hN.of_le
    (by simpa only [N, pow_two] using Nat.le_self_pow two_ne_zero n)
  have hpFit : Fits (w + 2) p := hmodfit.of_le (by omega)
  let a := initial.set one 1 |>.set 0 header |>.set size n |>.set 0 (header + 1) |>.set modulus p
    |>.set weights base |>.set area N |>.set 11 (N + N) |>.set 11 (N + N + N)
    |>.set 9 base |>.set 10 (base + (N + N + N)) |>.set residues (base + (N + N + N))
    |>.set counts (base + (N + N + N) + (N + N + N))
    |>.set queries (base + (N + N + N) + (N + N + N) + p) |>.set 12 (p + p)
  have hsetup : ExecWithin (w + 2) (setupAt header) initial a 15 := by
    dsimp [N, base] at hN h2N h3N hres hcounts hqueries
    ram_eval [setupAt, a, N, base, h1, hhead, hhead1, hbase, hN, h2N, h3N, hres,
      hcounts, hqueries, hmodfit, hsizeFit, hpFit,
      one, size, modulus, weights, area, residues, counts, queries,
      temp, weightLen, weightSrc, weightDst, encodedMod, hnHeader, hpHeader, Fin.mk.injEq]
  have ha9 : (a.comap (bank 16 (by decide))).regs Residues.src = base := by
    simp +decide [a, bank, Residues.src, one, size, modulus, weights, area, residues,
      counts, queries]
  have ha10 : (a.comap (bank 16 (by decide))).regs Residues.dst = base + 3 * N := by
    simp +decide [a, bank, Residues.dst, one, size, modulus, weights, area, residues,
      counts, queries]
    omega
  have ha11 : (a.comap (bank 16 (by decide))).regs Residues.len = 3 * N := by
    simp +decide [a, bank, Residues.len, one, size, modulus, weights, area, residues,
      counts, queries]
    omega
  have ha12 : (a.comap (bank 16 (by decide))).regs Residues.modulus = Signed.encode (p : ℤ) := by
    simp +decide [a, bank, Residues.modulus, one, size, modulus, weights, area, residues,
      counts, queries, Signed.encode, two_mul, show ¬(p : ℤ) < 0 by omega]
  obtain ⟨v, hv, hvm, -⟩ := Residues.exec (a.comap (bank 16 (by decide)))
    (fun q => values q) hp hmod ha12
    (by intro q hq; apply hvalues q; simpa only [ha11, N] using hq)
    (by rw [ha9, ha11]; exact haddress.of_le (by dsimp [addressBoundAt, N, base]; omega))
    (by rw [ha10, ha11]; exact haddress.of_le (by dsimp [addressBoundAt, N, base]; omega))
    (by rw [ha9, ha10, ha11])
    (by intro q hq; rw [ha9]; exact hinput q (by simpa only [ha11, N] using hq))
  let v' := v.extend (bank 16 (by decide)) a
  have hv' : ExecWithin (w + 2) reduce a v' (69 * N + 4) := by
    simpa only [reduce, v', ha11, ← Nat.mul_assoc, Nat.reduceMul] using
      hv.rename (bank_injective 16 (by decide))
  have hvreg (i : Fin 32) (hi : 24 ≤ i.val) : v'.regs i = a.regs i :=
    hv'.regs_eq (reduce_preserves i hi)
  have hvn : v'.regs size = n := by simpa +decide [a, size, modulus, weights, area,
    residues, counts, queries, one] using hvreg size (by decide)
  have hvp : v'.regs modulus = p := by simpa +decide [a, size, modulus, weights, area,
    residues, counts, queries, one] using hvreg modulus (by decide)
  have hvr : v'.regs residues = base + 3 * N := by
    have h := hvreg residues (by decide)
    simp +decide only [a, Data.set_regs, Function.update_apply, residues, counts, queries,
      ↓reduceIte] at h
    change v'.regs 27 = base + 3 * N
    omega
  have hvc : v'.regs counts = base + 6 * N := by
    have h := hvreg counts (by decide)
    simp +decide only [a, Data.set_regs, Function.update_apply, counts, queries, ↓reduceIte] at h
    change v'.regs 28 = base + 6 * N
    omega
  have hvq : v'.regs queries = base + 6 * N + p := by
    have h := hvreg queries (by decide)
    simp +decide only [a, Data.set_regs, Function.update_apply, queries, ↓reduceIte] at h
    change v'.regs 29 = base + 6 * N + p
    omega
  let b := v'.set 0 (base + 3 * N) |>.set 2 n |>.set 12 (base + 6 * N)
    |>.set 13 (base + 6 * N + p) |>.set 14 p
  have hdeliver : ExecWithin (w + 2) deliver v' b 5 := by
    ram_eval [deliver, b, hvn, hvp, hvr, hvc, hvq, residues, size, counts, queries,
      modulus, Fin.mk.injEq]
  have hb0 : (b.comap (bank 20 (by decide))).regs Classes.src = base + 3 * N := by
    simp +decide [b, bank, Classes.src]
  have hb2 : (b.comap (bank 20 (by decide))).regs Classes.size = n := by
    simp +decide [b, bank, Classes.size]
  have hb12 : (b.comap (bank 20 (by decide))).regs Classes.counts = base + 6 * N := by
    simp +decide [b, bank, Classes.counts]
  have hb13 : (b.comap (bank 20 (by decide))).regs Classes.queries = base + 6 * N + p := by
    simp +decide [b, bank, Classes.queries]
  have hb14 : (b.comap (bank 20 (by decide))).regs Classes.modulus = p := by
    simp +decide [b, bank, Classes.modulus]
  have hresmem (q : ℕ) (hq : q < 3 * N) : v.mem (base + 3 * N + q) = R q := by
    rw [hvm, ha10, ha11]
    simp only [Residues.memory]
    split_ifs with h
    swap
    · omega
    rw [show base + 3 * N + q - (base + 3 * N) = q by omega]
  obtain ⟨z, hz, -, hzcounts, hzpairs, hzframe⟩ := Classes.exec
    (b.comap (bank 20 (by decide))) R h1
    (by intro q hq; rw [hb0]; exact hresmem q (by rw [hb2] at hq; dsimp [N, base] at *; omega))
    (by rw [hb0, hb2, hb12]; dsimp [N, base]; omega)
    (by rw [hb12, hb14, hb13])
    (by rw [hb12, hb14]; exact haddress.of_le (by dsimp [addressBoundAt, N, base]; omega))
    (by rw [hb13, hb2, hb14]; exact haddress.of_le (by dsimp [addressBoundAt, N, base]; omega))
    (haddress.of_le (by rw [hb2]; dsimp [addressBoundAt, N, base]; omega))
  let y := z.extend (bank 20 (by decide)) b
  have hz' : ExecWithin (w + 2) classify b y (p * (14 * N + 14) + 6) := by
    simpa only [hb2, hb14, N, classify, y] using hz.rename (bank_injective 20 (by decide))
  have hyreg (i : Fin 32) (hi : 24 ≤ i.val) : y.regs i = v'.regs i := by
    have h := hz'.regs_eq (classify_preserves i hi)
    exact h.trans (by
      have h0 : i ≠ 0 := by intro heq; subst i; change 24 ≤ 0 at hi; omega
      have h2 : i ≠ 2 := by intro heq; subst i; change 24 ≤ 2 at hi; omega
      have h12 : i ≠ 12 := by intro heq; subst i; change 24 ≤ 12 at hi; omega
      have h13 : i ≠ 13 := by intro heq; subst i; change 24 ≤ 13 at hi; omega
      have h14 : i ≠ 14 := by intro heq; subst i; change 24 ≤ 14 at hi; omega
      simp only [b, Data.set_regs, Function.update_of_ne h0, Function.update_of_ne h2,
        Function.update_of_ne h12, Function.update_of_ne h13, Function.update_of_ne h14])
  simp only [hb2, hb12, hb13, hb14] at hzcounts hzpairs hzframe
  refine ⟨y, ?_, (hyreg residues (by decide)).trans hvr,
    (hyreg counts (by decide)).trans hvc, (hyreg queries (by decide)).trans hvq,
    ?_, hzcounts, hzpairs, ?_⟩
  · convert hsetup.seq (hv'.seq (hdeliver.seq hz')) using 1
    · rfl
    · dsimp [N, base]
      omega
  · intro q hq
    change z.mem (base + 3 * N + q) = R q
    rw [hzframe _ (by omega) (by omega)]
    exact hresmem q hq
  · intro a ha
    change z.mem a = initial.mem a
    rw [hzframe a (by rcases ha with h | h <;> omega) (by
      rcases ha with h | h
      · omega
      · exact not_lt_of_ge h ∘ And.right)]
    change v.mem a = initial.mem a
    rw [hvm, ha10, ha11]
    simp only [Residues.memory, show ¬(base + 3 * N ≤ a ∧ a < base + 3 * N + 3 * N) by
      rcases ha with h | h <;> omega, ↓reduceIte]
    rfl

/-- Read the input header, compute all three residue matrices and enumerate the A–B queries.
The signed width is `w`, and execution uses the existing signed compiler's `w+2` unsigned width.
The cost includes every header, reduction, argument-delivery and class-scan instruction; the
final halt is excluded. This subroutine does not choose a prime or solve an instance. -/
theorem exec_input {w : ℕ} (n p : ℕ) (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < values.length, GenericRAM.Signed.Fits w (values.getD q 0))
    (haddress : Fits (w + 2) (addressBound n p)) :
    ∃ y, ExecWithin (w + 2) program (.init (input n p values)) y
        (69 * (n * n) + p * (14 * (n * n) + 14) + 30) ∧
      y.regs residues = 3 + 3 * (n * n) ∧ y.regs counts = 3 + 6 * (n * n) ∧
      y.regs queries = 3 + 6 * (n * n) + p ∧
      (∀ q < 3 * (n * n), y.mem (3 + 3 * (n * n) + q) =
        (values.getD q 0 % (p : ℤ)).toNat) ∧
      (∀ j < p, y.mem (3 + 6 * (n * n) + j) =
        Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = j) (n * n)) ∧
      (∀ j < p, ∀ q < n * n, (values.getD q 0 % (p : ℤ)).toNat = j →
        y.mem (3 + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values.getD k 0 % (p : ℤ)).toNat = j) q) = q / n ∧
        y.mem (3 + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values.getD k 0 % (p : ℤ)).toNat = j) q + 1) = q % n) ∧
      (∀ a, a < 3 + 3 * (n * n) ∨
        3 + 6 * (n * n) + p + 2 * (n * n) * p ≤ a →
          y.mem a = (Data.init (input n p values) : Data 32).mem a) := by
  have h := exec_at (w := w) 1 n p (fun q => values.getD q 0) (.init (input n p values))
    (by simp [input, Data.init]) (by simp [input, Data.init])
    (fun q _ => input_weight n p values q) hp hmod
    (by intro q hq; exact hvalues q (by simpa only [hlen] using hq)) haddress
  simpa only [program, Nat.reduceAdd] using h

end Cslib.Algorithms.WordRAM.ExactTriangle.ResidueClasses
