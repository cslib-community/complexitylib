/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLabelLoad
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayBounds
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalSimulation

/-!
# Correctness of native local replay initialization

Explicit canonical windows agree with the existing embedded configuration's three blocks.
The work origins belong only to the semantic correspondence; loading retains relative cells.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Load

open MultiTapeNTM.ChoiceTable MultiTapeNTM.ConfigurationGraph

variable {k s : ℕ} {Q : Type}

/-- Canonical local buffers have exactly three blocks and use only the three cell codes. -/
@[expose] def CanonicalWindows (b : ℕ) : RawResult k Q → Prop :=
  fun (_, _, _, cells) => (∀ h, (cells h).length = 3 * b) ∧
    ∀ h n, n ∈ cells h → n ≤ 2

private theorem symbolCode_cellOfCode (n : ℕ) (hn : n ≤ 2) :
    symbolCode (cellOfCode n) = n := by
  have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

/-- Interpreting a raw canonical window preserves its explicit row-major cells. -/
private theorem windowCells_toView (b : ℕ) [NeZero b] (raw : RawResult k Q)
    (h : Fin k) (hlen : (raw.2.2.2 h).length = 3 * b) :
    windowCells b ((raw.toView b).2 h) = (raw.2.2.2 h).map cellOfCode := by
  apply List.ext_getElem
  · simp [windowCells, hlen]
  · intro i hi hright
    have hi' : i < 3 * b := by simpa only [windowCells, List.length_map,
      List.length_range] using hi
    have hd : i / b < 3 := (Nat.div_lt_iff_lt_mul (Nat.pos_of_neZero b)).mpr hi'
    simp only [windowCells, List.getElem_map, List.getElem_range, hd, ↓reduceDIte,
      RawResult.toView, ZMod.val_natCast]
    have hid : i / b * b + i % b = i := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i b
    rw [hid]
    have hc : i < (raw.2.2.2 h).length := by simpa only [List.length_map] using hright
    rw [List.getD_eq_getElem _ _ hc]

private theorem inputPos_eq (N b positive negative residue : ℕ) :
    inputPos N b positive negative residue =
      let p : ℤ := b * ((positive : ℤ) - negative) + residue % b + 1
      if 0 ≤ p ∧ p < N + 2 then p.toNat else 0 := by
  let hi := b * positive + residue % b + 1
  let lo := b * negative
  have hp : (b : ℤ) * ((positive : ℤ) - negative) + residue % b + 1 =
      (hi : ℤ) - lo := by dsimp only [hi, lo]; push_cast; ring
  rw [hp]
  change (if lo ≤ hi ∧ hi - lo < N + 2 then hi - lo else 0) = _
  by_cases hle : lo ≤ hi
  · have hcast : ((hi - lo : ℕ) : ℤ) = (hi : ℤ) - lo := Nat.cast_sub hle
    have hto : ((hi : ℤ) - lo).toNat = hi - lo := by rw [← hcast]; simp
    by_cases hb : hi - lo < N + 2
    · have hz : (hi : ℤ) - lo < N + 2 := by omega
      simp [hle, hb, hz, hto]
    · have hz : ¬ (hi : ℤ) - lo < N + 2 := by omega
      simp [hle, hb, hz]
  · simp [hle]

/-- Native loading is exactly the semantic view loader. Only the input block origin is stored
at runtime; work origins merely locate the unchanged relative windows in the correctness proof. -/
theorem load_eq_loadView (N b positive negative : ℕ) [NeZero b]
    (raw : RawResult k Q) (hcanonical : CanonicalWindows b raw)
    (J : Option (Fin k) → ℤ) (hinput : J none = (positive : ℤ) - negative) :
    load (N, b, (positive, negative), raw) = loadView N b J (raw.toView b) := by
  rcases raw with ⟨control, residues, track, cells⟩
  rcases hcanonical with ⟨hlen, hcodes⟩
  apply Config.ext
  · rfl
  · rfl
  · rfl
  · simp only [load, loadView, RawResult.toView, hinput, ZMod.val_natCast]
    exact inputPos_eq N b positive negative (residues none)
  · rfl
  · funext h
    simp only [load, loadView, RawResult.toView, ZMod.val_natCast]
  · funext h
    change cells h = List.ofFn (fun r : Fin (3 * b) => symbolCode (windowCell b J
      (RawResult.toView b (control, residues, track, cells)).2 h
        (b * (J (some h) - 1) + (r : ℤ))))
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hright
      have hi' : i < 3 * b := by simpa only [List.length_ofFn] using hright
      have hcell := windowCell_eq b J
        (RawResult.toView b (control, residues, track, cells)).2 h (i : ℤ)
      rw [ite_eq_left (Int.natCast_nonneg i), Int.toNat_natCast,
        windowCells_toView b (control, residues, track, cells) h (hlen h)] at hcell
      have hc : i < (cells h).length := hi
      rw [List.getElem_ofFn]
      rw [hcell]
      change (cells h)[i] = symbolCode (((cells h).map cellOfCode).getD i none)
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hc),
        List.getElem_map]
      exact (symbolCode_cellOfCode _ (hcodes h _ (List.getElem_mem hc))).symm
  · rfl

/-- The decoder constructs canonical explicit windows from every successful input label. -/
theorem canonical_of_parse_some (e : Q ≃ Fin s) (b : ℕ) (word : List Bool)
    (raw : RawResult k Q) (hp : Encoding.NativeDecode.parse e (b, word) = some raw) :
    CanonicalWindows b raw := by
  obtain ⟨_, hlen, _, rfl⟩ := (Encoding.NativeDecode.parse_eq_some_iff e b word raw).mp hp
  constructor
  · exact Encoding.NativeDecode.length_payload_cells_of_length e b word hlen
  · intro h n hn
    exact Encoding.NativeDecode.mem_cells_le _ n hn

/-- Canonical-code validation also provides the loader's concrete window invariants. -/
theorem canonical_of_checked_some (e : Q ≃ Fin s) (b : ℕ) (word : List Bool)
    (raw : RawResult k Q) (hp : Encoding.NativeChecked.parse e (b, word) = some raw) :
    CanonicalWindows b raw := by
  apply canonical_of_parse_some e b word raw
  dsimp only [Encoding.NativeChecked.parse] at hp
  split at hp
  · exact hp
  · contradiction

/-- Checked label loading agrees exactly with semantic loading after the tree gate's
canonical-code guard. FAIL and noncanonical labels never initialize a replay state. -/
theorem load_label_ofFn (e : Q ≃ Fin s) (N b positive negative : ℕ) [NeZero b]
    (bits : Cslib.BitString (Encoding.width k s b)) (J : Option (Fin k) → ℤ)
    (hinput : J none = (positive : ℤ) - negative) :
    Label.load e (N, b, (positive, negative), List.ofFn bits) =
      (decodeChecked (Encoding.encode e) (Encoding.decode e) bits).map
        (loadView N b J) := by
  have hd := Encoding.NativeChecked.parse_ofFn e b bits
  cases hp : Encoding.NativeChecked.parse (k := k) e (b, List.ofFn bits) with
  | none =>
    rw [hp, Option.map_none] at hd
    rw [← hd]
    simp only [Label.load, hp, Option.map_none]
  | some raw =>
    rw [hp, Option.map_some] at hd
    rw [← hd]
    simp only [Label.load, hp, Option.map_some]
    exact congrArg some (load_eq_loadView N b positive negative raw
      (canonical_of_checked_some e b (List.ofFn bits) raw hp) J hinput)

variable [Finite Q]

/-- Every physical clock of native-loaded canonical data has the proved local replay bound. -/
theorem length_runFrom_load_le (M : MultiTapeTM k Bool Q) (w : List Bool)
    (b positive negative : ℕ) [NeZero b] (raw : RawResult k Q)
    (hcanonical : CanonicalWindows b raw) (J : Option (Fin k) → ℤ)
    (hinput : J none = (positive : ℤ) - negative) (t : ℕ) :
    (encConfig ((machine M).runFrom w (load (w.length, b, (positive, negative), raw)) t)).length ≤
      1024 * (k + 1) * (b + Nat.log2 w.length + Nat.card (Option Q) +
        Nat.card OutputTrack + 1) := by
  rw [load_eq_loadView w.length b positive negative raw hcanonical J hinput]
  exact length_runFrom_loadView_le M w b J (raw.toView b) t

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Load
