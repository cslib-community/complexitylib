/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.GetD

/-!
# Reading a fixed prefix and a stored suffix

The original word is read-only input. Only a binary prefix length, a stored suffix and a binary
address enter the accessor state. `machine` emits one bit and halts: it reads the original input
at prefix addresses and indexes the stored suffix otherwise. All five query-machine components
have native charged space certificates linear in this small state, independently of the length
of the original word. `word` is a semantic specification and is never computed into workspace.
The false default agrees with `Turing.ReadMachine`.

This is the virtual-input access operation needed in the proof of Lemma 3.3 of
[GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047, printed page 6.
The paper's fixed prefix ends before its ceiling-logarithmic suffix. Initialization, query and
answer regeneration, suffix iteration and adaptive-to-tt conversion are separate obligations.
-/

public section

namespace Turing.VirtualWord

open MultiTapeTM

/-- The specified word; this list is not stored by the accessor. -/
@[expose] def word (x : List Bool) (cut : ℕ) (suffix : List Bool) : List Bool :=
  x.take cut ++ suffix

/-- The only stored data: prefix length, suffix and requested address. -/
abbrev Data := ℕ × List Bool × ℕ

/-- Binary counters and the literal stored suffix. -/
abbrev encData : Data ↪ List Bool := encPair encNat (encPair encBits encNat)

/-- State consists of the stored data and a halting bit. -/
abbrev State := Data × Bool

/-- The state encoding charges the stored suffix, but never the original prefix. -/
abbrev encState : State ↪ List Bool := encPair encData encBool

/-- Select the original input bit or a bit of the stored suffix, defaulting to false. -/
@[expose] def answer (d : Data) (b : Bool) : Bool :=
  if d.2.2 < d.1 then b else d.2.1.getD (d.2.2 - d.1) false

/-- One native input read suffices. The read is ignored at suffix addresses. -/
@[expose] def machine (d : Data) : QueryMachine State where
  init := (d, false)
  query s := s.1.2.2
  next p := (p.1.1, true)
  emit p := [answer p.1.1 (p.2.getD false)]
  halted := Prod.snd
  finish _ := []

/-- Exact length, including an empty prefix or suffix. -/
theorem length_word (x : List Bool) (cut : ℕ) (suffix : List Bool) (h : cut ≤ x.length) :
    (word x cut suffix).length = cut + suffix.length := by
  simp [word, Nat.min_eq_left h]

/-- Prefix, boundary, suffix and past-the-end reads all agree with the specified word. -/
theorem answer_eq_getD (x : List Bool) (cut : ℕ) (suffix : List Bool) (i : ℕ)
    (h : cut ≤ x.length) :
    answer (cut, suffix, i) (x.getD i false) = (word x cut suffix).getD i false := by
  simp only [answer, word, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_take, Nat.min_eq_left h]
  split_ifs with hi
  · simp [hi]
  · rfl

/-- The actual native run emits exactly the requested bit and then halts. -/
theorem output_one (d : Data) (x : List Bool) :
    (machine d).output x 1 = [answer d (x.getD d.2.2 false)] := by
  simp [QueryMachine.output, QueryMachine.run, QueryMachine.step, QueryMachine.read, machine,
    List.getD_eq_getElem?_getD]

/-- Only the halting bit changes; the stored suffix is never enlarged. -/
theorem run_one (d : Data) (x : List Bool) : (machine d).run x 1 = (d, true) := rfl

open ComputableInSpace

private theorem bitsGetD : ComputableInSpace
    (fun p : List Bool × ℕ => p.1.getD p.2 false) (encPair encBits encNat) encBool
    (fun p => (encPair encBits encNat p).length) := by
  have htail : ComputableInSpace List.tail encBits encBits (fun w => w.length) :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have h := iterate (snd encBits encNat) (fst encBits encNat) htail
    (Q := fun p => p.1.length) (B := fun p => p.1.length)
    (fun p i _ => by simp [List.tail_iterate]) (fun p i _ => by simp [List.tail_iterate])
  have hd : ComputableInSpace (fun p : List Bool × ℕ => p.1.drop p.2)
      (encPair encBits encNat) encBits (fun p => (encPair encBits encNat p).length) := by
    refine h.weaken (.of_le_linear 8 8 fun p => ?_) |>.of_enc_eq ?_
    · simp only [length_encPair, encBits_apply]; omega
    · intro p; rw [List.tail_iterate]
  have hh : ComputableInSpace (fun w : List Bool => w.headD false) encBits encBool
      (fun w => w.length) := of_inO (.of_linear (ListEncoding.headD false))
  refine (budget_comp_linear hh hd).of_enc_eq ?_
  intro p
  rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

/-- The selector is natively computable in charged space linear in the stored data and bit. -/
theorem answer_inSpace : ComputableInSpace (fun p : Data × Bool => answer p.1 p.2)
    (encPair encData encBool) encBool (fun p => (encPair encData encBool p).length) := by
  have hd := fst encData encBool
  have hc := hd.fst'
  have hs := hd.snd'.fst'
  have hi := hd.snd'.snd'
  have hlt := budget_comp_lin natLt (linear_succ) (budget_prod hi hc)
  have hsub := budget_natSub hi hc
  refine (budget_ite hlt (snd _ _)
    (budget_comp_linear bitsGetD (budget_prod hs hsub))).of_enc_eq ?_
  intro p
  simp [answer]

/-- All components of the accessor have native certificates in the small stored state. -/
theorem components_inSpace (d : Data) :
    ComputableInSpace (machine d).query encState encNat (fun s => (encState s).length) ∧
    ComputableInSpace (machine d).next (encPair encState (encOption encBool)) encState
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).emit (encPair encState (encOption encBool)) encBits
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).halted encState encBool (fun s => (encState s).length) ∧
    ComputableInSpace (machine d).finish encState encBits (fun s => (encState s).length) := by
  have hstate := fst encState (encOption encBool)
  have hdata := hstate.fst'
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd encState (encOption encBool))
  have ha := budget_comp_linear answer_inSpace (budget_prod hdata hb)
  refine ⟨(fst encData encBool).snd'.snd',
    budget_prod hdata (budget_const true (.refl _)), ?_, snd _ _, budget_const [] (.refl _)⟩
  exact budget_finite (encC := encBits) (fun b => [b]) ha

/-- Explicit storage bound: two binary counters, the suffix, and a halting bit. -/
theorem length_encState (cut i : ℕ) (suffix : List Bool) (halt : Bool) :
    (encState ((cut, suffix, i), halt)).length =
      4 * (encNat cut).length + 4 * suffix.length + 2 * (encNat i).length + 6 := by
  simp only [encState, encData, length_encPair, encBits_apply, encBool_apply, List.length_singleton]
  omega

/-- The native accessor uses the stored-state budget plus an input-position counter. The
original input is not part of the charged workspace. This theorem supplies actual multi-tape
machines, using the query-machine compiler, rather than assuming an access certificate. -/
theorem access_inSpace (d : Data) :
    ∃ t c, ComputableInTimeAndSpace
      (fun x : List Bool => answer d (x.getD d.2.2 false)) encBits encBool t
      (fun x => c * ((encState (d, false)).length + Nat.log2 x.length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace d
  refine (machine d).computableInSpace hq hn he hh hf (fun _ => 1)
    (fun _ => rfl) (fun x t ht => ?_) (fun x => ?_) _
    (fun _ => by simp only [encBits_apply]; omega) ⟨1, fun x t ht => ?_⟩
  · have : t = 0 := by omega
    subst t
    rfl
  · exact (output_one d x).symm
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · simp only [QueryMachine.run_zero, machine, Nat.one_mul]
      omega
    · rw [run_one]
      obtain ⟨cut, suffix, i⟩ := d
      simp only [length_encState, Nat.one_mul]
      omega

/-- A ceiling-logarithmic suffix and addresses at most the input length give an explicit
logarithmic state bound, including lengths zero and one. -/
theorem length_encState_le_log {n cut i : ℕ} {suffix : List Bool} (halt : Bool)
    (hc : cut ≤ n) (hi : i ≤ n) (hs : suffix.length ≤ Nat.clog 2 n) :
    (encState ((cut, suffix, i), halt)).length ≤ 16 * (Nat.log2 n + 1) := by
  have hcut := length_encNat_le_log2 hc
  have hindex := length_encNat_le_log2 hi
  have hclog : Nat.clog 2 n ≤ Nat.log2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_log2_self.le)
  rw [length_encState]
  omega

/-- A concrete logspace certificate on any input domain satisfying the stored-data bounds.
The domain hypotheses restrict data sizes, not correctness or an assumed resource certificate. -/
theorem access_inLogSpace (d : Data) (P : List Bool → Prop)
    (hcut : ∀ x, P x → d.1 ≤ x.length)
    (hindex : ∀ x, P x → d.2.2 ≤ x.length)
    (hsuffix : ∀ x, P x → d.2.1.length ≤ Nat.clog 2 x.length) :
    ComputableInLogSpace (fun x : {x // P x} => answer d (x.val.getD d.2.2 false))
      ((Function.Embedding.subtype P).trans encBits) encBool := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace d
  refine (machine d).computableInLogSpace hq hn he hh hf (fun _ => 1)
    (fun _ => rfl) (fun x t ht => ?_) (fun x => (output_one d x.val).symm)
    ⟨16, fun x t ht => ?_⟩
  · have : t = 0 := by omega
    subst t
    rfl
  · have hbound := length_encState_le_log (n := x.val.length)
      (cut := d.1) (i := d.2.2) (suffix := d.2.1)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · exact hbound false (hcut x.val x.property) (hindex x.val x.property)
        (hsuffix x.val x.property)
    · rw [run_one]
      exact hbound true (hcut x.val x.property) (hindex x.val x.property)
        (hsuffix x.val x.property)

end Turing.VirtualWord
