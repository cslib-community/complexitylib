/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Registers

/-!
# Deterministic edges throughout the compact configuration box

The guarded compact graph of a deterministic machine has at most one successor at every ID,
including invalid and unreachable IDs. This does not require a decoder or a represented-view
hypothesis.

The argument is the register-level one. A compact edge is a register step between the registers
read from its endpoints, with the supplied symbol read through `inputSymbol`
(`registerStepWith_of_edgeWithSymbol`); a deterministic machine steps uniquely on register tuples
(`rightUnique_registerStepWith`); and IDs below `vertexBound B` are determined by their registers
(`readRegisters_injOn`).

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.pack_readRegisters_of_lt_vertexBound`,
  `Turing.MultiTapeNTM.ConfigurationGraph.readRegisters_injOn`: IDs below `vertexBound B` are
  recovered from, and so determined by, their registers.
* `Turing.MultiTapeNTM.ConfigurationGraph.registerStepWith_of_edgeWithSymbol`: a compact edge is a
  register step between the registers of its endpoints.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_target_unique`: target uniqueness for
  the compact graph of a deterministic machine.
* `Turing.MultiTapeNTM.ConfigurationGraph.sum_edgeWithSymbol_le_one`: each indicator row has
  total mass at most one, including rows truncated by the radix bound.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- Every compact ID strictly below `vertexBound B` has positive radix `B`. -/
theorem radix_pos_of_lt_vertexBound {B u : ℕ} (hu : u < vertexBound (k := k) B) : 0 < B := by
  rcases Nat.eq_zero_or_pos B with rfl | hpos
  · have : Nonempty (Register k) := ⟨.inputPos⟩
    have hcard : Fintype.card (Register k) ≠ 0 := Fintype.card_ne_zero
    simp [vertexBound, zero_pow hcard] at hu
  · exact hpos

/-- Packing `readRegisters B u` recovers any compact ID `u < vertexBound B`. -/
theorem pack_readRegisters_of_lt_vertexBound {B u : ℕ} (hu : u < vertexBound (k := k) B) :
    Cslib.Radix.pack B (readRegisters (k := k) B u) = u := by
  have hB : 0 < B := radix_pos_of_lt_vertexBound hu
  obtain ⟨x, hx, hval⟩ := Nat.exists_ofDigits_ofFn (B := B) (d := Fintype.card (Register k)) hu
  let f : Register k → ℕ := fun i => x (Fintype.equivFin (Register k) i)
  have hf_lt : ∀ i, f i < B := fun i => hx _
  have hpack_f : Cslib.Radix.pack B f = u := by
    unfold Cslib.Radix.pack
    simpa only [f, Equiv.apply_symm_apply] using hval
  have hread : readRegisters (k := k) B u = f := by
    funext i
    rw [← hpack_f]
    exact Cslib.Radix.component_pack hB hf_lt i
  rw [hread, hpack_f]

/-- IDs below `vertexBound B` are determined by the registers read from them. -/
theorem readRegisters_injOn {B u v : ℕ} (hu : u < vertexBound (k := k) B)
    (hv : v < vertexBound (k := k) B)
    (h : readRegisters (k := k) B u = readRegisters (k := k) B v) : u = v := by
  rw [← pack_readRegisters_of_lt_vertexBound hu, ← pack_readRegisters_of_lt_vertexBound hv, h]

/-- **A compact edge is a register step** between the registers read from its endpoints, for the
input length `n` and the supplied symbol read through `inputSymbol`. -/
theorem registerStepWith_of_edgeWithSymbol {ntm : MultiTapeNTM k Bool State}
    {B n u v : ℕ} {symbol : Option Bool} (h : edgeWithSymbol ntm B n u v symbol = true) :
    RegisterStepWith ntm n (fun p => inputSymbol n p symbol) (readRegisters (k := k) B u)
      (readRegisters (k := k) B v) := by
  simp only [edgeWithSymbol, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h.2 with ⟨hc, rfl⟩ | ⟨t, ht, ⟨⟨hm, hfit⟩, rfl⟩⟩
  · exact .inl ⟨hc, rfl⟩
  · simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_ofFn, id_eq] at hm
    refine .inr ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, (mem_instructions ntm t).mp ht, hm.1.1, hm.1.2,
      fun i => of_decide_eq_true (hm.2 _ ⟨i, rfl⟩), ?_⟩
    have hf := fitsB_eq_true.mp hfit
    funext i
    exact Cslib.Radix.component_pack (pos_of_fits hf) hf i

/-- The compact graph of a deterministic machine has at most one target for each source and
supplied input symbol. The statement includes all IDs, with no validity or reachability premise. -/
theorem edgeWithSymbol_target_unique (tm : MultiTapeTM k Bool State)
    {B n u v z : ℕ} {symbol : Option Bool}
    (hv : edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true)
    (hz : edgeWithSymbol tm.toMultiTapeNTM B n u z symbol = true) : v = z :=
  readRegisters_injOn (lt_vertexBound_of_edgeWithSymbol hv).2
    (lt_vertexBound_of_edgeWithSymbol hz).2
    (rightUnique_registerStepWith tm.deterministic n _ (registerStepWith_of_edgeWithSymbol hv)
      (registerStepWith_of_edgeWithSymbol hz))

/-- Summing a deterministic edge indicator over the entire compact box gives at most one.
Invalid IDs and radix-overflowing transitions may give a row of zeros. -/
theorem sum_edgeWithSymbol_le_one (tm : MultiTapeTM k Bool State)
    (B n u : ℕ) (symbol : Option Bool) :
    ∑ v : Fin (vertexBound (k := k) B),
      (edgeWithSymbol tm.toMultiTapeNTM B n u v symbol).toNat ≤ 1 := by
  classical
  by_cases h : ∃ v : Fin (vertexBound (k := k) B),
      edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = true
  · obtain ⟨v, hv⟩ := h
    rw [Finset.sum_eq_single v]
    · simp [hv]
    · intro z _ hz
      have he : edgeWithSymbol tm.toMultiTapeNTM B n u z symbol = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        exact hz (Fin.ext (edgeWithSymbol_target_unique tm he hv))
      simp [he]
    · simp
  · have he (v : Fin (vertexBound (k := k) B)) :
        edgeWithSymbol tm.toMultiTapeNTM B n u v symbol = false :=
      Bool.eq_false_iff.mpr fun hv => h ⟨v, hv⟩
    simp [he]

end Turing.MultiTapeNTM.ConfigurationGraph
