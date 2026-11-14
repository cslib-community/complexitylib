/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.BitEncryption.CoinTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Tactic.Linarith
import CslibFrontier.Tactic.EncLen

/-!
# Callback-sensitive native bounds for bit-encryption replay

The existing saved-tape evaluator retains separate callback time, workspace and ciphertext-size
bounds. Its preparation polynomial is chosen before the callback and its bounds. Every actual
padded row is charged, including on short tapes; no well-formed tape premise is imposed.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.exists_encryptBitsCoins_time_bound`: native replay with
  linear dependence on the maximum participating callback time and separate peak workspace.

These are original quantitative execution refinements. They do not compare primitive encryption
costs with an adversary's runtime or establish Gentry's relative reduction-runtime bound.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Turing.MultiTapeTM

/-- The polynomial for preparing the actual seed rows is independent of the encryption callback
and of its time, workspace and output bounds. Only participating rows need satisfy those bounds.
Every padded row is an actual encryption seed, so the ciphertext bound is derived from encryption
support even for malformed tapes. Big-O constants may depend on the fixed callback certificate.
The workspace charge retains the serialized ciphertext list and the largest callback workspace.
All input functions, including the unary seed width and the complete raw tape, are charged. -/
theorem exists_encryptBitsCoins_time_bound
    {α : Type} {input : α ↪ List Bool} {n encCoins : α → ℕ}
    {pk bits tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hcoins : ComputableInPolyTime encCoins input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧
      ∀ (E : Scheme) (evaluate : (ℕ × List Bool × Bool) → List Bool → List Bool)
        (T S : (ℕ × List Bool × Bool) × List Bool → ℕ),
      ComputableInO (fun p => evaluate p.1 p.2)
        (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits T S →
      (∀ a, ∀ bit ∈ bits a, ProbComp.eval (E.encrypt (n a) (pk a) bit) =
        (BitString.uniformList (encCoins a)).map (evaluate (n a, pk a, bit))) →
      ∀ R Q L : α → ℕ,
      (∀ a, ∀ row ∈ (bits a).zip (BitString.listRows (bits a).length (encCoins a) (tape a)),
        T ((n a, pk a, row.1), row.2) ≤ R a) →
      (∀ a, ∀ row ∈ (bits a).zip (BitString.listRows (bits a).length (encCoins a) (tape a)),
        S ((n a, pk a, row.1), row.2) ≤ Q a) →
      (∀ a, ∀ bit ∈ bits a, ∀ ciphertext ∈
        (ProbComp.eval (E.encrypt (n a) (pk a) bit)).support, ciphertext.length ≤ L a) →
      ComputableInO (fun a => encryptBitsCoins evaluate (n a) (encCoins a)
        (pk a) (bits a) (tape a)) input (encList encBits)
        (fun a => P (input a).length + ((bits a).length + 1) *
          (R a + (bits a).length * (L a + 1)))
        (fun a => P (input a).length + Q a + (bits a).length * (L a + 1)) := by
  let par := fun a => (n a, pk a)
  let rows := fun a => (bits a).zip
    (BitString.listRows (bits a).length (encCoins a) (tape a))
  let encP := encPair encUnary encBits
  let encR := encPair encBool encBits
  have hrows : ComputableInPolyTime rows input (encList encR) := by
    have hblocks : ComputableInPolyTime (fun a =>
        BitString.listRows (bits a).length (encCoins a) (tape a))
        input (encList encBits) := by fun_prop
    exact (ComputableInPolyTime.zip encBool encBits).comp
      ((ComputableInPolyTime.bitsToList.comp hbits).prod hblocks)
  have hprepare : ComputableInPolyTime (fun a => (par a, rows a)) input
      (encPair encP (encList encR)) := (hn.prod hpk).prod hrows
  obtain ⟨t, s, ht, hs, k, State, hfinite, machine, hmachine⟩ := hprepare
  let B := fun size => size + t size + s size + 1
  have hB : PolynomiallyBounded B := by dsimp only [B]; fun_prop
  have hp : ComputableInO (fun a => (par a, rows a)) input
      (encPair encP (encList encR)) (fun a => B (input a).length)
      (fun a => B (input a).length) := by
    refine ComputableInO.of_bounds ⟨k, State, hfinite, machine, hmachine⟩ 1 ?_ ?_ ?_
    · intro a; dsimp only [B]; omega
    · intro a; dsimp only [B]; omega
    · intro a
      have h := (hmachine a).length_output_le
      change (encPair encP (encList encR) (par a, rows a)).length ≤ t (input a).length at h
      dsimp only [B]
      omega
  have hparSize (a : α) : (encP (par a)).length ≤ B (input a).length := by
    have := (hmachine a).length_output_le
    simp only [length_encPair] at this
    dsimp only [B]
    omega
  have hrowsSize (a : α) : (encList encR (rows a)).length ≤ B (input a).length := by
    have := (hmachine a).length_output_le
    simp only [length_encPair] at this
    dsimp only [B]
    omega
  have hrowsLength (a : α) : (rows a).length = (bits a).length := by
    simp [rows]
  have hcount (a : α) : (bits a).length ≤ B (input a).length := by
    rw [← hrowsLength]
    exact (length_le_length_encList encR (rows a)).trans (hrowsSize a)
  refine ⟨fun size => 40 * (B size + 1) ^ 2, by fun_prop, ?_⟩
  intro E evaluate T S hevaluate hencrypt R Q L htime hspace hciphertext
  have hlength (a : α) (row : Bool × List Bool) (hrow : row ∈ rows a) :
      (evaluate (n a, pk a, row.1) row.2).length ≤ L a := by
    obtain ⟨hbit, hseed⟩ := List.of_mem_zip hrow
    apply hciphertext a row.1 hbit
    rw [hencrypt a row.1 hbit]
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨row.2, BitString.mem_support_uniformList_iff.mpr
      (BitString.length_of_mem_listRows hseed), rfl⟩
  have hleft := ComputableInO.fst encP encR
  have hright := ComputableInO.snd encP encR
  have hcall : ComputableInO
      (fun p : (ℕ × List Bool) × (Bool × List Bool) =>
        ((p.1.1, p.1.2, p.2.1), p.2.2)) (encPair encP encR)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits)
      (fun p => 4 * (encPair encP encR p).length)
      (fun p => 4 * (encPair encP encR p).length) := by
    convert (hleft.fst'.prod (hleft.snd'.prod hright.fst')).prod hright.snd' using 1 <;>
      funext p <;> omega
  have hstep : ComputableInO
      (fun p : (ℕ × List Bool) × (Bool × List Bool) =>
        evaluate (p.1.1, p.1.2, p.2.1) p.2.2) (encPair encP encR) encBits
      (fun p => 4 * (encPair encP encR p).length + T ((p.1.1, p.1.2, p.2.1), p.2.2))
      (fun p => 4 * (encPair encP encR p).length + S ((p.1.1, p.1.2, p.2.1), p.2.2)) :=
    hevaluate.comp hcall
  have hmap := ComputableInO.mapWith (par := par) (list := rows) hstep hp.fst' hp.snd' 
  have hrowSize (a : α) (row : Bool × List Bool) (hrow : row ∈ rows a) :
      (encPair encP encR (par a, row)).length ≤ 3 * B (input a).length + 1 := by
    have h := length_le_encList_of_mem encR hrow
    have := hparSize a
    have := hrowsSize a
    enc_len
  have htimeMax (a : α) : listMax
      (fun row => 4 * (encPair encP encR (par a, row)).length +
        T ((n a, pk a, row.1), row.2)) (rows a) ≤
        4 * (3 * B (input a).length + 1) + R a := by
    apply listMax_le
    intro row hrow
    have := hrowSize a row hrow
    have := htime a row hrow
    omega
  have hspaceMax (a : α) : listMax
      (fun row => 4 * (encPair encP encR (par a, row)).length +
        S ((n a, pk a, row.1), row.2)) (rows a) ≤
        4 * (3 * B (input a).length + 1) + Q a := by
    apply listMax_le
    intro row hrow
    have := hrowSize a row hrow
    have := hspace a row hrow
    omega
  have hout (a : α) : (encList encBits
      ((rows a).map (fun row => evaluate (n a, pk a, row.1) row.2))).length ≤
      (bits a).length * (2 * L a + 1) + 1 := by
    have h := length_encList_le encBits
      ((rows a).map (fun row => evaluate (n a, pk a, row.1) row.2)) (b := L a) (by
        intro value hvalue
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hvalue
        exact hlength a row hrow)
    rw [List.length_map, hrowsLength] at h
    exact h.trans (Nat.le_succ _)
  have hmap' : ComputableInO
      (fun a => (rows a).map (fun row => evaluate (n a, pk a, row.1) row.2))
      input (encList encBits)
      (fun a => (input a).length + B (input a).length + B (input a).length +
        ((rows a).length + 1) * ((encP (par a)).length + (encList encR (rows a)).length +
          (encList encBits ((rows a).map
            (fun row => evaluate (n a, pk a, row.1) row.2))).length +
          listMax (fun row => 4 * (encPair encP encR (par a, row)).length +
            T ((n a, pk a, row.1), row.2)) (rows a)))
      (fun a => (input a).length + B (input a).length + B (input a).length +
        (encP (par a)).length + (encList encR (rows a)).length +
          (encList encBits ((rows a).map
            (fun row => evaluate (n a, pk a, row.1) row.2))).length +
          listMax (fun row => 4 * (encPair encP encR (par a, row)).length +
            S ((n a, pk a, row.1), row.2)) (rows a)) := by
    exact hmap
  refine (hmap'.mono 2 (fun a => ?_) (fun a => ?_)).of_enc_eq fun a => ?_
  · have hM : (input a).length ≤ B (input a).length := by dsimp only [B]; omega
    have := hparSize a
    have := hrowsSize a
    have := hcount a
    have := htimeMax a
    have := hout a
    rw [hrowsLength]
    nlinarith
  · have hM : (input a).length ≤ B (input a).length := by dsimp only [B]; omega
    have := hparSize a
    have := hrowsSize a
    have := hspaceMax a
    have := hout a
    nlinarith
  · congr 1
    exact List.map_uncurry_zip_eq_zipWith.symm

end Cslib.Crypto.Homomorphic.Scheme
