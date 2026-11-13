/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Complexity.Classes.Sparse.Envelope
import CslibFrontier.Computability.Complexity.Classes.Sparse.Meyer
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness

/-! # Source-correspondence clients for Goldreich Chapter 3 theory exercises

Exercise 3.2(2) uses ordinary bit languages and adaptive polynomial-time oracle reductions;
3.5 identifies the union of the oracle classes. Exercise 3.12 permits a nonsparse decidable
envelope: in particular, the envelope can be the full bit-language domain.
-/

open Cslib Cslib.Complexity Cslib.Circuits.Boolean Turing.MultiTapeTM

-- Exercise 3.2(2), translating the encoded-instance API to ordinary circuit languages.
example (L : Language Bool) : L ∈ PPoly ↔
    ∃ S ∈ SPARSE encBits, (L : Set (List Bool)) ∈ PWithOracle S encBits := by
  rw [← mem_PPolyOn_encBits_iff]
  exact mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle

-- Exercise 3.5 identifies exactly the class of problems reducible to a suitable oracle.
example (L : Set (List Bool)) : L ∈ NP encBits ∩ coNP encBits ↔
    ∃ A ∈ NP encBits ∩ coNP encBits, L ∈ PWithOracle A encBits := by
  conv_lhs => rw [← iUnion_PWithOracle_NP_inter_coNP]
  simp only [Set.mem_iUnion, exists_prop]

-- Exercise 3.12: the envelope itself can be nonsparse, including the full domain.
example {S : Set (List Bool)} (hS : Sᶜ ∈ SPARSE encBits)
    (hred : PolyTimeReducible encCNF encBits SAT S) : SAT ∈ P encCNF :=
  SAT_mem_P_of_sparse_diff (G := Set.univ) (Set.subset_univ S) univ_mem_P
    (by simpa only [Set.compl_eq_univ_sdiff] using hS) hred

example : (Set.univ : Set (List Bool)) ∉ SPARSE encBits := univ_notMem_SPARSE
