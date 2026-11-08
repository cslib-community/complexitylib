/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceUniformSparseCounter
public import Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
public import Complexity.Computability.Complexity.FineGrained.SparseParitySchedule

/-!
# Actual native incidence counter in the greedy parity reduction

Instantiate the executable parity reduction with the native incidence counter, including every
candidate tested and discarded by greedy search. Declared unused variables remain counted.
Correctness covers polylogarithmic-density leaves at all sizes. The certificate has global
polynomial workspace and an explicit split-time bound charging all candidates and initial-row
search. Absorption of that overhead and the general-density counting-sparsification schedule
remain separate obligations; this is not Lemma 3.2 for arbitrary density.

This implements the polylogarithmic-density leaf step of Appendix D.3, p. 57 in
[OpenAI2026ETH], toward the general-density counter imported by Lemma 3.2 of
[Counting Exact-One Hitting Sets][ChenJiangZhu2027].
The source Lemma 3.2 is for every fixed width at least two, all declared sizes at least 20
and unrestricted clause density; the leaf theorem here has the explicit density restriction.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString
open Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Logic.PL Cslib.Logic.PL.CNF SparseCNFLeafCounter

/-- Fixed sparse-system parameter accommodating every parity candidate. -/
@[expose] def paritySparsity (β : ℕ) : ℕ := max 6 (2 * β + 4)

/-- A fixed cutoff, independent of the formula and its desired count. -/
@[expose] def parityCutoff (k β : ℕ) : ℕ :=
  2 ^ (initialRowWeightCoeff 1 β * 2 ^ k + 1)

/-- Every compiled candidate, not only the greedy winners, satisfies the native sparse domain. -/
theorem compiledSystem_isSparse {k β n m : ℕ} {sys : List (List (List ℕ))}
    (hn : parityCutoff k β ≤ n) (hm : m ≤ Nat.clog 2 n ^ β * n)
    (hs : IsCompiledSparseSystem k n (6 * n)
      (initialRowWeightBound (Nat.clog 2 n ^ β) m * 2 ^ k) sys) :
    SubexponentialSAT.IncidenceBranching.IsSparseSystem k (paritySparsity β) n sys := by
  simp only [parityCutoff] at hn
  have hlog : initialRowWeightCoeff 1 β * 2 ^ k + 1 ≤ Nat.clog 2 n :=
    (Nat.clog_pow 2 _ Nat.one_lt_two).symm.trans_le
      (Nat.clog_mono_right 2 (show 2 ^ _ ≤ n from hn))
  have hn2 : 2 ≤ n := (Nat.pow_le_pow_right (by decide : 0 < 2)
    (by omega : 1 ≤ initialRowWeightCoeff 1 β * 2 ^ k + 1)).trans (show 2 ^ _ ≤ n from hn)
  have hlam : 1 ≤ Nat.clog 2 n := by omega
  have hW := initialRowWeightBound_le_mul_pow_clog hn2 hm
    (by simp : Nat.clog 2 n ^ β ≤ 1 * Nat.clog 2 n ^ β)
  have hterms : initialRowWeightBound (Nat.clog 2 n ^ β) m * 2 ^ k ≤
      Nat.clog 2 n ^ paritySparsity β := by
    calc
      _ ≤ (initialRowWeightCoeff 1 β * 2 ^ k) * Nat.clog 2 n ^ (2 * β + 3) := by
        simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_right (2 ^ k) hW
      _ ≤ Nat.clog 2 n * Nat.clog 2 n ^ (2 * β + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = Nat.clog 2 n ^ (2 * β + 4) :=
        ((pow_succ (Nat.clog 2 n) (2 * β + 3)).trans (Nat.mul_comm _ _)).symm
      _ ≤ _ := Nat.pow_le_pow_right hlam (le_max_right _ _)
  exact ⟨fun eq he mon hm v hv => ((hs.2 eq he).2.2 mon hm).2 v hv,
    fun eq he => (hs.2 eq he).1,
    hs.1.trans (Nat.mul_le_mul_right n (le_max_left _ _)),
    fun eq he => (hs.2 eq he).2.1.trans hterms,
    fun eq he mon hm => ((hs.2 eq he).2.2 mon hm).1⟩

/-- Actual greedy parity search with the guarded native counter, preserving declared dimension. -/
@[expose] noncomputable def countParity (k β N₀ : ℕ) : ℕ × CNF ℕ → ℕ :=
  sparseCNFDeclaredCounter id (fun n => Nat.clog 2 n ^ β) k (parityCutoff k β)
    (uniformSparseCount k (paritySparsity β) N₀)

/-- The executable cap bounds binary output even on inputs outside the correctness domain. -/
theorem countParity_le (k β N₀ : ℕ) (x : ℕ × CNF ℕ) : countParity k β N₀ x ≤ 2 ^ x.1 :=
  sparseCNFDeclaredCounter_le_two_pow id (fun n => Nat.clog 2 n ^ β) k
    (parityCutoff k β) (uniformSparseCount k (paritySparsity β) N₀) x

/-- Original assignment count, including the empty formula and unused declared variables.
The only density restriction is on the leaf formula; no counter-correctness premise is supplied. -/
theorem countParity_eq_modelCountOn {k β N₀ n : ℕ} {ψ : CNF ℕ}
    (hw : ∀ clause ∈ ψ, clause.length ≤ k)
    (hv : ψ.vars.toFinset ⊆ Finset.range n)
    (hm : ψ.length ≤ Nat.clog 2 n ^ β * n ∨ n < parityCutoff k β) :
    countParity k β N₀ (n, ψ) = ψ.modelCountOn (Finset.range n) := by
  apply sparseCNFDeclaredCounter_eq_modelCountOn hw hv
    (hm.elim Or.inl (fun h => Or.inr (Or.inr (Or.inr h))))
  intro hn sys hs
  change parityCutoff k β ≤ n at hn
  have hm' : ψ.length ≤ Nat.clog 2 n ^ β * n := hm.resolve_right (by omega)
  simp only [id_eq] at hs ⊢
  rw [uniformSparseCount_eq_rootCount (compiledSystem_isSparse hn hm' hs)]
  exact HeavyBranchFold.rootCount_eq_commonZeroCount
    (fun eq he => (hs.2 eq he).1)
    (fun eq he mon hm v hv => ((hs.2 eq he).2.2 mon hm).2 v hv)

private theorem density_polytime (β : ℕ) :
    ComputableInPolyTime (fun n => Nat.clog 2 n ^ β) encUnary encUnary := by
  induction β with
  | zero => exact const 1
  | succ β ih =>
    simpa only [pow_succ, Function.comp_def] using
      unary_mul' ih (binary_clog_two.comp unary_to_binary)

/-- Actual parity machine, with global polynomial workspace and an explicit time bound.
The bound charges the initial search and every candidate evaluation; it assumes no callback
resource conclusion. Its remaining parity overhead is not asserted to be absorbed into eta. -/
theorem exists_countParity_certificate (k β : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ D : ℕ, ∃ cs : NativeCertificate (countParity k β N₀)
      (encPair encUnary encCNF) encNat,
    ∃ poly qInit polySys : ℕ → ℕ,
      Cslib.PolynomiallyBounded poly ∧ Cslib.PolynomiallyBounded qInit ∧
      Cslib.PolynomiallyBounded polySys ∧ ∀ x : ℕ × CNF ℕ,
        cs.space x ≤ poly (encPair encUnary encCNF x).length ∧
        cs.time x ≤ 2 * (sparseCNFTimeBound encUnary id (fun n => Nat.clog 2 n ^ β)
          k (parityCutoff k β) poly qInit
          (fun y => D * (polySys (encPair encUnary encCNF y).length + 1) ^ D *
            2 ^ (D * Nat.logLogSqrtLogScale y.1)) x + 1) := by
  obtain ⟨N₀, cp, D, hp⟩ := exists_uniformSparseCount_certificate k (paritySparsity β) hk
  have hspace : PolyBounded (fun p : ArrayInput => (encArrayInput p).length) cp.space :=
    (PolyBounded.of_polynomiallyBounded
      (fun p : ArrayInput => (encArrayInput p).length)
      (bound := fun L => D * (L + 1) ^ D) (by fun_prop)).mono (fun p => (hp p).2)
  let cs := sparseCNFDeclaredCertificate k (parityCutoff k β)
    (id' (encIn := encUnary)) (density_polytime β) cp
  obtain ⟨poly, qInit, polySys, hpoly, hq, hsys, hs, ht⟩ :=
    exists_sparseCNFDeclaredCertificate_bounds k (parityCutoff k β)
      (id' (encIn := encUnary)) (density_polytime β) cp hspace
  refine ⟨N₀, D, cs, poly, qInit, polySys, hpoly, hq, hsys, fun x => ⟨hs x, ?_⟩⟩
  apply ht
  unfold ValidPolyTimeBound
  intro y _ sys _ hlen
  exact (hp (y.1, sys)).1.trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) D)))

end Cslib.Circuits.Frontier.IncidenceNetwork
