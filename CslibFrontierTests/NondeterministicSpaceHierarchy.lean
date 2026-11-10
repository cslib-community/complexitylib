/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicSpace
public import CslibFrontierTests.UniversalNondeterministic

/-! The nondeterministic diagonal within space. The machine `coin`, which emits either bit, accepts
every input; read off its description, it accepts within any budget above the size of its
configurations, so the diagonal within space `(n + 1) ^ 2` rejects its padded description. The
diagonal within space `(n + 1) ^ 2` is not in nondeterministic linear space, and the diagonal within
space `4 * log₂ n` is not in nondeterministic constant space. -/

public section

namespace CslibFrontierTests.NondeterministicSpaceHierarchy

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter
open CslibFrontierTests.UniversalNondeterministic

/-! ### The bridge and the diagonal on a concrete machine -/

/-- `coin` runs within no cells, so its description accepts within any budget above the size of
its configurations. -/
example (input : List Bool) {b : ℕ}
    (hb : cfgSpaceBound (descLen (descN eUnit eBit coin)) input.length 0 0 ≤ b) :
    BAccepts (descN eUnit eBit coin) (input.map eBit) b :=
  (accepts_iff_bAccepts_descN eUnit coin (by simp) hb).mp (coin_accepts input)

/-- The diagonal within space `(n + 1) ^ 2` rejects the padded description of `coin`, which accepts
every input. -/
example (pad : List Bool) (hpad : 2 ^ 2 ^ (eDesc (descN eUnit eBit coin)).length ≤ pad.length) :
    frame (eDesc (descN eUnit eBit coin)) ++ pad ∉ nspaceDiagonal fun n => (n + 1) ^ 2 := by
  have hpow := Nat.one_le_two_pow (n := 2 ^ (eDesc (descN eUnit eBit coin)).length)
  have hD : 2 ≤ (eDesc (descN eUnit eBit coin)).length := by
    simp only [eDesc_apply, length_encPair]
    omega
  have hdec : decodeDesc (Diagonal.tinyCut (frame (eDesc (descN eUnit eBit coin)) ++ pad)) =
      descN eUnit eBit coin := by
    rw [Diagonal.tinyCut_of_tinyDesc (Diagonal.tinyDesc_frame_append hpad),
      decodeDesc_unframe_frame_append]
  have hlen : (frame (eDesc (descN eUnit eBit coin)) ++ pad).length =
      2 * (eDesc (descN eUnit eBit coin)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  generalize frame (eDesc (descN eUnit eBit coin)) ++ pad = x at hdec hlen
  have hn : (encNat (x.length + 1)).length ≤ Nat.log2 x.length + 2 :=
    length_encNat_le_log2_add_two le_rfl
  have hl := Nat.log2_le_self x.length
  have h6 : 6 ≤ x.length := by omega
  have hb : cfgSpaceBound (descLen (descN eUnit eBit coin)) x.length 0 0 ≤ (x.length + 1) ^ 2 := by
    simp only [cfgSpaceBound, descLen]
    nlinarith [Nat.mul_le_mul_right x.length h6]
  rw [nspaceDiagonal, Set.mem_ofPred_eq, hdec, not_not]
  exact (accepts_iff_bAccepts_descN eUnit coin (by simp) hb).mp (coin_accepts x)

/-! ### The lower bound on concrete bounds -/

/-- The diagonal within space `(n + 1) ^ 2` is not in nondeterministic linear space. -/
example : nspaceDiagonal (fun n => (n + 1) ^ 2) ∉ NSPACE encBits fun n => n :=
  nspaceDiagonal_notMem_NSPACE
    (fun n => (Nat.mul_le_mul_left 4 (Nat.log2_le_self n)).trans
      (by nlinarith [sq_nonneg ((n : ℤ) - 1)])) fun c => by
    filter_upwards [eventually_ge_atTop c] with n hc
    nlinarith

/-- At the logarithmic threshold: the diagonal within space `4 * log₂ n` is not in
nondeterministic constant space. -/
example : nspaceDiagonal (fun n => 4 * Nat.log2 n) ∉ NSPACE encBits fun _ => 1 :=
  nspaceDiagonal_notMem_NSPACE (fun _ => le_rfl) fun c => by
    filter_upwards [eventually_ge_atTop (2 ^ (2 * c))] with n hn
    have := (Nat.le_log2 (by have := Nat.one_le_two_pow (n := 2 * c); omega)).mpr hn
    omega

end CslibFrontierTests.NondeterministicSpaceHierarchy
