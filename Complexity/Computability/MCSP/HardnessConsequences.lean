/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH.KarpLipton
public import Complexity.Computability.Complexity.Classes.ZPP
public import Complexity.Computability.MCSP.NP
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Complexity.Classes.Hierarchy.Nondeterministic
import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Structural consequences of the NP-hardness of MCSP

If the Minimum Circuit Size Problem (`Cslib.MCSP`) is `NP`-hard under polynomial-time many-one
reductions (`Cslib.Complexity.NPHard`), several structural collapses and class separations follow
[Murray and Williams][MurrayWilliams2017]:

1. **Collapse of `NEXP` to `EXP` under `EXP ⊆ P/poly`**
   (`Cslib.Complexity.NEXP_subset_EXP_of_MCSP_npHard_of_EXP_subset_PPoly`,
   `Cslib.Complexity.EXP_eq_NEXP_of_MCSP_npHard_of_EXP_subset_PPoly`,
   [Murray and Williams, Section 4.1, Theorem 4.1, p. 13][MurrayWilliams2017]):
   Murray and Williams state Theorem 4.1 as:
   > "If every sparse language in `NP` has a polynomial-time reduction to `MCSP`, then
   > `EXP ⊂ P/poly ⟹ EXP = NEXP`."

   The Lean theorems here assume full `NPHard MCSP.encInstance MCSP` (which implies the hypothesis
   for every language in `NP`, and in particular every tally/sparse language in `NP`), so they
   formalize the full-`NPHard` specialization of Theorem 4.1. For any problem `A ∈ NEXP`, its
   exponentially padded version `ntm.padded c` lies in `NP`, and the `NP`-hardness reduction `R`
   (applied only to `ntm.padded c`) maps padded instances `z (enc a)` of length `2 ^ poly(|enc a|)`
   to `MCSP` instances `R (z (enc a))`. Reading the `(R (z (enc a))).table` bit at position `y`
   defines a problem in `EXP` on pairs `(enc a, y)`, hence in `P/poly` when `EXP ⊆ P/poly`.
   Hardwiring `enc a` into the `P/poly` circuits bounds the circuit complexity of
   `(R (z (enc a))).function` by a fixed polynomial `s_bound |enc a|` on arity `m_bound |enc a|`.
   Consequently, membership of `R (z (enc a))` in `MCSP` depends only on the capped threshold
   `min (s_bound |enc a|) (R (z (enc a))).threshold`, and brute-force enumeration of all circuit
   certificates of that size (`Cslib.MCSP.boundedMCSPSearch`) takes time `2 ^ poly(|enc a|)` and
   decides `A` in `EXP`.
2. **Separation `EXP ⊈ NP ∩ P/poly` and `EXP ≠ ZPP`**
   (`Cslib.Complexity.not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard`,
   `Cslib.Complexity.EXP_ne_NP_inter_PPolyOn_of_MCSP_npHard`,
   `Cslib.Complexity.not_EXP_subset_RP_of_MCSP_npHard`,
   `Cslib.Complexity.not_EXP_subset_ZPP_of_MCSP_npHard`,
   `Cslib.Complexity.EXP_ne_ZPP_of_MCSP_npHard`,
   [Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]):
   Murray and Williams state Theorem 1.6 as:
   > "If `MCSP` is `NP`-hard under polynomial-time reductions, then `EXP ≠ NP ∩ P/poly`.
   > Consequently, `EXP ≠ ZPP`."

   Combining Theorem 4.1 with `NEXP ⊈ NP` (`Cslib.Complexity.not_NEXP_subset_NP`, proved in
   `Complexity.Computability.Complexity.Classes.Hierarchy.Nondeterministic` by double-exponential
   padding from the deterministic time hierarchy) shows that `EXP ⊆ NP ∩ P/poly` (equivalently
   `EXP = NP ∩ P/poly`, since `NP ∩ P/poly ⊆ NP ⊆ EXP`) is impossible if `MCSP` is `NP`-hard.
   As an immediate corollary via `ZPP ⊆ RP ⊆ NP ∩ P/poly` (`RP_subset_NP`, `RP_subset_PPolyOn`),
   `NP`-hardness of `MCSP` under arbitrary polynomial-time many-one reductions implies `EXP ⊈ RP`
   and `EXP ≠ ZPP`.
3. **Karp–Lipton collapse from `MCSP ∈ P/poly`**
   (`Cslib.Complexity.NP_subset_PPolyOn_of_MCSP_npHard_of_mem_PPolyOn`,
   `Cslib.Complexity.PH_eq_SigmaP_two_of_MCSP_npHard_of_mem_PPolyOn`):
   If `MCSP` is both `NP`-hard and in `P/poly`, then `NP ⊆ P/poly` and the polynomial hierarchy
   collapses to `Σ₂`.

## Main definitions

* `Cslib.MCSP.boundedMCSPSearch`: brute-force circuit search up to a unary gate budget `S` and
  unary certificate-enumeration budget `K`.

## Main results

* `Cslib.MCSP.computableInPolyTime_boundedMCSPSearch`,
  `Cslib.MCSP.boundedMCSPSearch_eq_true_iff`,
  `Cslib.MCSP.boundedMCSPSearch_ofFn_eq_true_iff`: polynomial-time complexity and correctness of
  bounded circuit search.
* `Cslib.Complexity.NEXP_subset_EXP_of_MCSP_npHard_of_EXP_subset_PPoly`,
  `Cslib.Complexity.EXP_eq_NEXP_of_MCSP_npHard_of_EXP_subset_PPoly`: full-`NPHard` specialization
  of Murray–Williams Theorem 4.1 (`EXP ⊆ P/poly ⟹ EXP = NEXP`).
* `Cslib.Complexity.not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard`,
  `Cslib.Complexity.EXP_ne_NP_inter_PPolyOn_of_MCSP_npHard`: Murray–Williams Theorem 1.6
  (`EXP ≠ NP ∩ P/poly` from `NP`-hardness of `MCSP`).
* `Cslib.Complexity.not_EXP_subset_RP_of_MCSP_npHard`,
  `Cslib.Complexity.EXP_ne_RP_of_MCSP_npHard`,
  `Cslib.Complexity.not_EXP_subset_ZPP_of_MCSP_npHard`,
  `Cslib.Complexity.EXP_ne_ZPP_of_MCSP_npHard`: corollaries `EXP ⊈ RP` and `EXP ≠ ZPP` from
  `NP`-hardness of `MCSP`.
* `Cslib.Complexity.NP_subset_PPolyOn_of_MCSP_npHard_of_mem_PPolyOn`,
  `Cslib.Complexity.PH_eq_SigmaP_two_of_MCSP_npHard_of_mem_PPolyOn`: if `MCSP` is `NP`-hard and in
  `P/poly`, then `NP ⊆ P/poly` and `PH = Σ₂`.

## References

* [C. D. Murray, R. R. Williams, *On the (non) NP-hardness of computing circuit
  complexity*][MurrayWilliams2017]
-/

@[expose] public section

namespace Cslib.Complexity

open Filter _root_.Turing _root_.Turing.MultiTapeTM Circuits Circuits.Boolean

/-! ### Pair decoding and lifting `EXP ⊆ P/poly` to pairs of bitstrings -/

/-- Decode an encoded pair of bitstrings `frame u ++ v` into `(unframe w, dropFrame w)`. -/
private def decodePair (w : List Bool) : List Bool × List Bool :=
  (unframe w, dropFrame w)

/-- `decodePair` is a left inverse of `encPair encBits encBits`. -/
private theorem decodePair_encPair (p : List Bool × List Bool) :
    decodePair (encPair encBits encBits p) = p :=
  Prod.ext (by simp [decodePair]) (by simp [decodePair])

/-- `decodePair` is computable in polynomial time. -/
private theorem computableInPolyTime_decodePair :
    ComputableInPolyTime decodePair encBits (encPair encBits encBits) :=
  ComputableInPolyTime.unframe.prod ComputableInPolyTime.dropFrame

/-- Re-encoding `decodePair w` increases the word length by at most `1`. -/
private theorem length_encPair_decodePair_le :
    ∀ w : List Bool, (encPair encBits encBits (decodePair w)).length ≤ w.length + 1
  | [] => by simp [decodePair, unframe, dropFrame]
  | [false] => by simp [decodePair, unframe, dropFrame]
  | [true] => by simp [decodePair, unframe, dropFrame]
  | false :: b :: v => by simp [decodePair, unframe, dropFrame]
  | true :: b :: v => by
    have ih := length_encPair_decodePair_le v
    simp only [decodePair, unframe, dropFrame, length_encPair, encBits_apply,
      List.length_cons] at ih ⊢
    omega

/-- If `EXP encBits ⊆ PPolyOn encBits`, then `EXP` on paired bitstrings `encPair encBits encBits`
also lies in `PPolyOn (encPair encBits encBits)`. -/
private theorem EXP_encPair_subset_PPolyOn_of_EXP_subset_PPoly
    (hEXP : EXP encBits ⊆ PPolyOn encBits) :
    EXP (encPair encBits encBits) ⊆ PPolyOn (encPair encBits encBits) := by
  intro L hL
  obtain ⟨k, hk⟩ := mem_EXP_iff.mp hL
  have hk' : L ∈ DTIME (encPair encBits encBits) fun m => 2 ^ m ^ (k + 1) :=
    DTIME_mono_of_eventually_le (eventually_atTop.mpr ⟨1, fun m hm =>
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hm (Nat.le_succ k))⟩) hk
  have hdecO : ComputableInO decodePair encBits (encPair encBits encBits)
      (fun w => w.length + w.length) (fun w => w.length + w.length) :=
    (ComputableInO.of_linear (.of_unframe fun _ => rfl)).prod
      (ComputableInO.of_linear (.of_dropFrame fun _ => rfl))
  have hpre : decodePair ⁻¹' L ∈ DTIME encBits fun n => 2 ^ (n + 1) ^ (k + 1) := by
    refine preimage_mem_DTIME (C := 3) hk' hdecO fun w => ?_
    set n := w.length
    have h₁ : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_self_pow (by omega) (n + 1)
    have h₂ : (n + 1) ^ (k + 1) ≤ 2 ^ (n + 1) ^ (k + 1) := Nat.lt_two_pow_self.le
    have h₃ : n ≤ 2 ^ (n + 1) ^ (k + 1) := by omega
    have h₄ : 2 ^ (encPair encBits encBits (decodePair w)).length ^ (k + 1) ≤
        2 ^ (n + 1) ^ (k + 1) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_left (length_encPair_decodePair_le w) (k + 1))
    change n + n + 2 ^ (encPair encBits encBits (decodePair w)).length ^ (k + 1) ≤
      3 * 2 ^ (n + 1) ^ (k + 1) + 3
    omega
  have hpre_EXP : decodePair ⁻¹' L ∈ EXP encBits := by
    refine mem_EXP_iff.mpr ⟨2 * (k + 1), DTIME_mono_of_eventually_le
      (eventually_atTop.mpr ⟨2, fun n hn => Nat.pow_le_pow_right (by norm_num) ?_⟩) hpre⟩
    have hn2 : n + 1 ≤ n ^ 2 := by nlinarith
    calc (n + 1) ^ (k + 1)
        ≤ (n ^ 2) ^ (k + 1) := Nat.pow_le_pow_left hn2 (k + 1)
      _ = n ^ (2 * (k + 1)) := (pow_mul n 2 (k + 1)).symm
  have hpre_PPoly : decodePair ⁻¹' L ∈ PPolyOn encBits := hEXP hpre_EXP
  have hred : PolyTimeReducible (encPair encBits encBits) encBits L (decodePair ⁻¹' L) :=
    ⟨encPair encBits encBits, .of_eq fun _ => rfl, fun p => by
      change p ∈ L ↔ decodePair (encPair encBits encBits p) ∈ L
      rw [decodePair_encPair]⟩
  exact hred.mem_PPolyOn hpre_PPoly

end Cslib.Complexity

/-! ### Bounded brute-force certificate search for MCSP -/

namespace Cslib.MCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity
open ComputableInPolyTime

/-- Certificate length is monotone in both the input arity and the gate budget. -/
private theorem certLength_mono {m₁ m₂ s₁ s₂ : ℕ} (hm : m₁ ≤ m₂) (hs : s₁ ≤ s₂) :
    certLength m₁ s₁ ≤ certLength m₂ s₂ := by
  unfold certLength
  gcongr

/-- Check whether a truth table `T` (of arity `m = Nat.log 2 T.length`) has a circuit of size at
most `S` by enumerating all certificates of length `min (certLength m S) (Nat.log 2 K)`. Because
the certificate length is capped at `Nat.log 2 K`, at most `K + 1` certificates are enumerated, so
the search runs in time polynomial in `T.length`, `S`, and `K` when `S` and `K` are given in
unary. -/
def boundedMCSPSearch (T : List Bool) (S K : ℕ) : Bool :=
  let m := Nat.log 2 T.length
  let cLen := min (certLength m S) (Nat.log 2 K)
  (BitString.enumList cLen).any fun u =>
    checkCertificate (fun y out => out == tableValue T y) m S u

/-- `boundedMCSPSearch` is computable in polynomial time when the truth table `T` is given as bits
and the gate budget `S` and enumeration budget `K` are given in unary. -/
@[fun_prop]
theorem computableInPolyTime_boundedMCSPSearch {γ : Type} {encIn : γ ↪ List Bool}
    {T : γ → List Bool} {S K : γ → ℕ}
    (hT : ComputableInPolyTime T encIn encBits)
    (hS : ComputableInPolyTime S encIn encUnary)
    (hK : ComputableInPolyTime K encIn encUnary) :
    ComputableInPolyTime (fun a => boundedMCSPSearch (T a) (S a) (K a)) encIn encBool := by
  let m (a : γ) : ℕ := Nat.log 2 (T a).length
  let cLen (a : γ) : ℕ := min (certLength (m a) (S a)) (Nat.log 2 (K a))
  have hm : ComputableInPolyTime m encIn encUnary :=
    binary_log_two.comp (unary_to_binary.comp (length_bits.comp hT))
  have hcLen : ComputableInPolyTime cLen encIn encUnary := by
    change ComputableInPolyTime
      (fun a => min (certLength (m a) (S a)) (Nat.log 2 (K a))) encIn encUnary
    have hcert : ComputableInPolyTime (fun a => certLength (m a) (S a)) encIn encUnary := by
      unfold certLength
      fun_prop
    have hlogK : ComputableInPolyTime (fun a => Nat.log 2 (K a)) encIn encUnary :=
      binary_log_two.comp (unary_to_binary.comp hK)
    simpa only [Nat.min_def] using ite_decide (unary_le' hcert hlogK) hcert hlogK
  obtain ⟨c_K, d_K, hK_len⟩ := hK.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hK_len
  let size_enum (L : ℕ) : ℕ := 2 * (c_K * (L + 1) ^ d_K + 1) ^ 2
  have hsize_enum : PolynomiallyBounded size_enum := by
    unfold size_enum
    fun_prop
  have hbudget_enum (a : γ) :
      2 ^ cLen a * (2 * cLen a + 1) ≤ size_enum (encIn a).length := by
    have hc_le_log : cLen a ≤ Nat.log 2 (K a) := Nat.min_le_right _ _
    have hlog_le : Nat.log 2 (K a) ≤ K a := Nat.log_le_self 2 (K a)
    have hpow_le : 2 ^ cLen a ≤ K a + 1 := by
      calc 2 ^ cLen a
          ≤ 2 ^ Nat.log 2 (K a) := Nat.pow_le_pow_right (by norm_num) hc_le_log
        _ ≤ K a + 1 := by
          rcases Nat.eq_zero_or_pos (K a) with h0 | hpos
          · simp [h0]
          · exact (Nat.pow_log_le_self 2 hpos.ne').trans (Nat.le_succ _)
    have hlin_le : 2 * cLen a + 1 ≤ 2 * (K a + 1) := by omega
    have hKa : K a + 1 ≤ c_K * ((encIn a).length + 1) ^ d_K + 1 :=
      Nat.add_le_add_right (hK_len a) 1
    calc 2 ^ cLen a * (2 * cLen a + 1)
        ≤ (K a + 1) * (2 * (K a + 1)) := Nat.mul_le_mul hpow_le hlin_le
      _ = 2 * (K a + 1) ^ 2 := by ring
      _ ≤ 2 * (c_K * ((encIn a).length + 1) ^ d_K + 1) ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hKa 2)
  have henum : ComputableInPolyTime (fun a => BitString.enumList (cLen a))
      encIn (encList encBits) :=
    bitsEnumList hcLen hsize_enum hbudget_enum
  obtain ⟨c_T, d_T, hT_len⟩ := hT.polyBounded_length.exists_le
  simp only [encBits_apply] at hT_len
  let size_T (L : ℕ) : ℕ := 2 * (c_T * (L + 1) ^ d_T + 1) ^ 2
  have hsize_T : PolynomiallyBounded size_T := by
    unfold size_T
    fun_prop
  have hbudget_T (p : γ × List Bool) :
      2 ^ m p.1 * (2 * m p.1 + 1) ≤ size_T (encPair encIn encBits p).length := by
    set lenT := (T p.1).length
    have hpow : 2 ^ m p.1 ≤ lenT + 1 := by
      rcases Nat.eq_zero_or_pos lenT with h0 | hpos
      · simp [m, lenT, h0]
      · exact (Nat.pow_log_le_self 2 hpos.ne').trans (Nat.le_succ _)
    have hlog : 2 * m p.1 + 1 ≤ 2 * (lenT + 1) := by
      have : m p.1 ≤ lenT := Nat.log_le_self 2 lenT
      omega
    have hlen_p : (encIn p.1).length ≤ (encPair encIn encBits p).length :=
      length_le_encPair_left encIn encBits p
    have hlenT_le : lenT + 1 ≤ c_T * ((encPair encIn encBits p).length + 1) ^ d_T + 1 := by
      calc lenT + 1
          ≤ c_T * ((encIn p.1).length + 1) ^ d_T + 1 := Nat.add_le_add_right (hT_len p.1) 1
        _ ≤ c_T * ((encPair encIn encBits p).length + 1) ^ d_T + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_left c_T (Nat.pow_le_pow_left (by omega) d_T)) 1
    calc 2 ^ m p.1 * (2 * m p.1 + 1)
        ≤ (lenT + 1) * (2 * (lenT + 1)) := Nat.mul_le_mul hpow hlog
      _ = 2 * (lenT + 1) ^ 2 := by ring
      _ ≤ 2 * (c_T * ((encPair encIn encBits p).length + 1) ^ d_T + 1) ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlenT_le 2)
  have haccept : ComputableInPolyTime
      (fun q : ((γ × List Bool) × List Bool) × Bool =>
        q.2 == tableValue (T q.1.1.1) q.1.2)
      (encPair (encPair (encPair encIn encBits) encBits) encBool) encBool := by
    have hval : ComputableInPolyTime
        (fun q : ((γ × List Bool) × List Bool) × Bool => tableValue (T q.1.1.1) q.1.2)
        (encPair (encPair (encPair encIn encBits) encBits) encBool) encBool :=
      computableInPolyTime_tableValue.comp
        ((hT.comp (fst _ _).fst'.fst').prod (fst _ _).snd')
    exact (snd _ _).beq hval
  have hcheck : ComputableInPolyTime
      (fun p : γ × List Bool =>
        checkCertificate (fun y out => out == tableValue (T p.1) y) (m p.1) (S p.1) p.2)
      (encPair encIn encBits) encBool :=
    computableInPolyTime_checkCertificate
      (hm.comp (fst _ _)) (hS.comp (fst _ _)) (snd _ _)
      hsize_T hbudget_T haccept
  exact anyWithInput henum hcheck

/-- When `T` has length `2 ^ m` and the enumeration budget satisfies
`certLength m S ≤ Nat.log 2 K`, `boundedMCSPSearch T S K` returns `true` if and only if the
Boolean function represented by `T` has circuit complexity at most `S`. -/
theorem boundedMCSPSearch_eq_true_iff {m S K : ℕ} {T : List Bool} (hT : T.length = 2 ^ m)
    (hK : certLength m S ≤ Nat.log 2 K) :
    boundedMCSPSearch T S K = true ↔
      complexity interpretation (single (tableFunction m T)) ≤ S := by
  have hm : Nat.log 2 T.length = m := by rw [hT, Nat.log_pow Nat.one_lt_two]
  unfold boundedMCSPSearch
  dsimp only
  rw [hm, Nat.min_eq_left hK]
  simp only [List.any_eq_true, BitString.mem_enumList]
  constructor
  · rintro ⟨u, -, hu⟩
    obtain ⟨c, hcS, hall⟩ := exists_circuit_of_checkCertificate hu
    refine complexity_le_iff.2 ⟨c, Circuit.computes_single_iff.2 fun y => ?_, hcS⟩
    have hy := hall y
    simp only [beq_iff_eq] at hy
    exact hy
  · intro hcomp
    obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
      (f := single (tableFunction m T))
    have hcS : c.size ≤ S := hsize ▸ hcomp
    obtain ⟨u, hu_len, hV⟩ := exists_checkCertificate_append
      (accept := fun y out => out == tableValue T y) hcS fun y => by
        rw [Circuit.computes_single_iff.1 hc y]
        exact beq_self_eq_true _
    exact ⟨u, hu_len, by simpa using hV []⟩

/-- On the truth table `List.ofFn x.table` of an `MCSP.Instance` `x`, when
`certLength x.arity S ≤ Nat.log 2 K`, `boundedMCSPSearch` decides whether `x.function` has
circuit complexity at most `S`. -/
theorem boundedMCSPSearch_ofFn_eq_true_iff (x : Instance) {S K : ℕ}
    (hK : certLength x.arity S ≤ Nat.log 2 K) :
    boundedMCSPSearch (List.ofFn x.table) S K = true ↔
      complexity interpretation (single x.function) ≤ S := by
  rw [boundedMCSPSearch_eq_true_iff List.length_ofFn hK]
  have hfun : tableFunction x.arity (List.ofFn x.table) = x.function := by
    funext y
    exact tableValue_ofFn x y
  rw [hfun]

end Cslib.MCSP

/-! ### Murray–Williams Theorem 4.1, Theorem 1.6, and Karp–Lipton consequences -/

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Circuits Circuits.Boolean MCSP

/-- **Murray–Williams Theorem 4.1 (`NEXP ⊆ EXP`, full-`NPHard` specialization)**
[Murray and Williams, Section 4.1, Theorem 4.1, p. 13][MurrayWilliams2017]:
> "If every sparse language in `NP` has a polynomial-time reduction to `MCSP`, then
> `EXP ⊂ P/poly ⟹ EXP = NEXP`."

This theorem assumes full `NPHard MCSP.encInstance MCSP` (which implies the hypothesis for every
language in `NP`, and in particular every tally/sparse language in `NP`; the proof applies `hHard`
only to the unary-padded language `ntm.padded c`), and shows that if `EXP encBits ⊆ PPolyOn encBits`
then `NEXP enc ⊆ EXP enc` for every encoding `enc` of instances. -/
theorem NEXP_subset_EXP_of_MCSP_npHard_of_EXP_subset_PPoly
    (hHard : NPHard MCSP.encInstance MCSP) (hEXP : EXP encBits ⊆ PPolyOn encBits)
    {α : Type} (enc : α ↪ List Bool) :
    NEXP enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NEXP_iff.mp hA
  obtain ⟨c₁, c₂, k_tapes, State, hfinite, ntm, hdec⟩ := hk
  set c := Nat.card (Turing.Action k_tapes Bool State) * (c₁ + c₂)
  obtain ⟨R, hR, hR_iff⟩ := hHard encBits (ntm.padded c) (ntm.padded_mem_NP c)
  let f (n : ℕ) : ℕ := n ^ (k + 1) + 1
  have hf : ComputableInPolyTime f encUnary encUnary := by
    unfold f
    fun_prop
  have hnf (n : ℕ) : n ≤ f n :=
    (Nat.le_self_pow (by omega) n).trans (Nat.le_succ _)
  let z (x : List Bool) : List Bool := frame x ++ List.replicate (2 ^ f x.length) true
  have hR_pair : ComputableInPolyTime
      (fun w : List Bool => (List.ofFn (R w).table, (R w).threshold))
      encBits (encPair encBits encNat) :=
    hR.of_enc_eq (encD := encPair encBits encNat) fun _ => rfl
  have hR_table : ComputableInPolyTime (fun w : List Bool => List.ofFn (R w).table)
      encBits encBits :=
    (ComputableInPolyTime.fst encBits encNat).comp hR_pair
  have hR_thresh : ComputableInPolyTime (fun w : List Bool => (R w).threshold)
      encBits encNat :=
    (ComputableInPolyTime.snd encBits encNat).comp hR_pair
  let B_bit : Set (List Bool × List Bool) :=
    {q : List Bool × List Bool | tableValue (List.ofFn (R q.1).table) q.2 = true}
  have hB_bit : B_bit ∈ P (encPair encBits encBits) :=
    ⟨fun q => tableValue (List.ofFn (R q.1).table) q.2,
      computableInPolyTime_tableValue.comp
        ((hR_table.comp (ComputableInPolyTime.fst encBits encBits)).prod
          (ComputableInPolyTime.snd encBits encBits)),
      fun _ => Iff.rfl⟩
  let L_pad : Set (List Bool × List Bool) :=
    (fun p : List Bool × List Bool => (z p.1, p.2)) ⁻¹' B_bit
  have hL_pad_EXP : L_pad ∈ EXP (encPair encBits encBits) :=
    preimage_pad_prod_id_mem_EXP (enc := encBits) hB_bit hf
  obtain ⟨M, hM_PPoly, hM⟩ := EXP_encPair_subset_PPolyOn_of_EXP_subset_PPoly hEXP hL_pad_EXP
  obtain ⟨c_R, d_R, hR_len⟩ := hR.polyBounded_length.exists_le
  simp only [encBits_apply] at hR_len
  obtain ⟨c_M, d_M, hM_size⟩ := polynomiallyBounded_iff_le.mp hM_PPoly
  let m_bound (n : ℕ) : ℕ := c_R + (f n + 2) * d_R
  let s_bound (n : ℕ) : ℕ := c_M * (2 * n + 1 + m_bound n + 1) ^ d_M + 2
  let g (n : ℕ) : ℕ := certLength (m_bound n) (s_bound n) + n
  have harity (x : List Bool) : (R (z x)).arity ≤ m_bound x.length := by
    set n := x.length
    have h2_arity : 2 ^ (R (z x)).arity ≤ (MCSP.encInstance (R (z x))).length := by
      rw [MCSP.encInstance_apply, length_encPair, encBits_apply, List.length_ofFn]
      omega
    have hn_le : n + 1 ≤ 2 ^ f n :=
      (Nat.lt_two_pow_self (n := n)).trans_le (Nat.pow_le_pow_right (by norm_num) (hnf n))
    have hzx_len : (z x).length + 1 ≤ 2 ^ (f n + 2) := by
      simp only [z, List.length_append, length_frame, List.length_replicate, pow_add]
      change 2 * n + 1 + 2 ^ f n + 1 ≤ 2 ^ f n * 4
      omega
    have hpow_le : 2 ^ (R (z x)).arity ≤ 2 ^ m_bound n := by
      calc 2 ^ (R (z x)).arity
          ≤ (MCSP.encInstance (R (z x))).length := h2_arity
        _ ≤ c_R * ((z x).length + 1) ^ d_R := hR_len (z x)
        _ ≤ 2 ^ c_R * (2 ^ (f n + 2)) ^ d_R :=
            Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hzx_len d_R)
        _ = 2 ^ m_bound n := by simp only [m_bound, ← pow_mul, ← pow_add]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  have hcomp_le (x : List Bool) :
      complexity interpretation (single (R (z x)).function) ≤ s_bound x.length := by
    let a_frame : Fin (frame x).length → Bool := fun j => (frame x)[j]
    have ha_frame : List.ofFn a_frame = frame x := List.ofFn_getElem
    have hslice : (R (z x)).function =
        fun y => M.slice ((frame x).length + (R (z x)).arity)
          (substitute (prependInputs a_frame) y) := by
      funext y
      have hMx := hM (x, List.ofFn y)
      rw [encPair_apply, encBits_apply] at hMx
      rw [Bool.eq_iff_iff, ← tableValue_ofFn, Language.slice_eq_true_iff,
        substitute_prependInputs, List.ofFn_fin_append, ha_frame]
      exact hMx
    have hc : complexity interpretation (single (R (z x)).function) ≤
        complexity interpretation (single (M.slice (2 * x.length + 1 + (R (z x)).arity))) + 2 := by
      have hc₀ := complexity_substitute_le (prependInputs a_frame)
        (M.slice ((frame x).length + (R (z x)).arity))
      rwa [← hslice, length_frame] at hc₀
    have hm_le := harity x
    calc complexity interpretation (single (R (z x)).function)
        ≤ complexity interpretation
            (single (M.slice (2 * x.length + 1 + (R (z x)).arity))) + 2 := hc
      _ ≤ c_M * (2 * x.length + 1 + (R (z x)).arity + 1) ^ d_M + 2 :=
          Nat.add_le_add_right (hM_size _) 2
      _ ≤ c_M * (2 * x.length + 1 + m_bound x.length + 1) ^ d_M + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left c_M
            (Nat.pow_le_pow_left (by omega) d_M)) 2
  -- Compose the unary bounds explicitly: one `fun_prop` over the unfolded nest is too slow.
  have hid : ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary := .id'
  have hc (a : ℕ) : ComputableInPolyTime (fun _ : ℕ => a) encUnary encUnary := .const a
  have hadd {u v : ℕ → ℕ} (hu : ComputableInPolyTime u encUnary encUnary)
      (hv : ComputableInPolyTime v encUnary encUnary) :
      ComputableInPolyTime (fun n => u n + v n) encUnary encUnary :=
    ComputableInPolyTime.unary_add.comp (hu.prod hv)
  have hmul {u v : ℕ → ℕ} (hu : ComputableInPolyTime u encUnary encUnary)
      (hv : ComputableInPolyTime v encUnary encUnary) :
      ComputableInPolyTime (fun n => u n * v n) encUnary encUnary :=
    ComputableInPolyTime.unary_mul.comp (hu.prod hv)
  have hm_bound : ComputableInPolyTime m_bound encUnary encUnary :=
    hadd (hc c_R) (hmul (hadd hf (hc 2)) (hc d_R))
  have hs_bound : ComputableInPolyTime s_bound encUnary encUnary :=
    hadd (hmul (hc c_M) ((ComputableInPolyTime.unary_pow d_M).comp
      (hadd (hadd (hadd (hmul (hc 2) hid) (hc 1)) hm_bound) (hc 1)))) (hc 2)
  have hg : ComputableInPolyTime g encUnary encUnary := by
    have hns := hadd hm_bound hs_bound
    exact hadd (hadd (hadd hs_bound hns) (hmul hs_bound (hadd (hc 3) (hmul (hc 2) hns)))) hid
  let B_search : Set (List Bool × ℕ) :=
    {p : List Bool × ℕ |
      boundedMCSPSearch (List.ofFn (R p.1).table)
        (min (s_bound (unframe p.1).length) (R p.1).threshold) p.2 = true}
  have hB_search : B_search ∈ P (encPair encBits encUnary) := by
    let encIn := encPair encBits encUnary
    have hunframe_len : ComputableInPolyTime (fun p : List Bool × ℕ => (unframe p.1).length)
        encIn encUnary :=
      ComputableInPolyTime.length_bits.comp
        (ComputableInPolyTime.unframe.comp (ComputableInPolyTime.fst encBits encUnary))
    have hcap : ComputableInPolyTime
        (fun p : List Bool × ℕ => s_bound (unframe p.1).length) encIn encUnary :=
      hs_bound.comp hunframe_len
    have hS : ComputableInPolyTime
        (fun p : List Bool × ℕ => min (s_bound (unframe p.1).length) (R p.1).threshold)
        encIn encUnary :=
      ComputableInPolyTime.binary_min_unary' hcap
        (hR_thresh.comp (ComputableInPolyTime.fst encBits encUnary))
    exact ⟨_, computableInPolyTime_boundedMCSPSearch
      (hR_table.comp (ComputableInPolyTime.fst encBits encUnary))
      hS (ComputableInPolyTime.snd encBits encUnary), fun _ => Iff.rfl⟩
  have hEXP_pre :
      (fun a : α => (z (enc a), 2 ^ g (enc a).length)) ⁻¹' B_search ∈ EXP enc :=
    preimage_pad_prod_two_pow_mem_EXP hB_search hf hnf hg
  have hA_eq : A = (fun a : α => (z (enc a), 2 ^ g (enc a).length)) ⁻¹' B_search := by
    ext a
    set x := enc a
    set n := x.length
    have hunframe_zx : (unframe (z x)).length = n := by
      simp [z, n]
    have hcert_le :
        certLength (R (z x)).arity (min (s_bound n) (R (z x)).threshold) ≤
          Nat.log 2 (2 ^ g n) := by
      rw [Nat.log_pow Nat.one_lt_two]
      exact (certLength_mono (harity x) (Nat.min_le_left _ _)).trans (Nat.le_add_right _ n)
    have hsearch_iff :
        (z x, 2 ^ g n) ∈ B_search ↔ R (z x) ∈ MCSP := by
      change boundedMCSPSearch (List.ofFn (R (z x)).table)
        (min (s_bound (unframe (z x)).length) (R (z x)).threshold) (2 ^ g n) = true ↔
        R (z x) ∈ MCSP
      rw [hunframe_zx, boundedMCSPSearch_ofFn_eq_true_iff (R (z x)) hcert_le,
        le_min_iff, MCSP.mem_iff]
      exact ⟨fun h => h.2, fun h => ⟨hcomp_le x, h⟩⟩
    have hpad_iff : a ∈ A ↔ z x ∈ ntm.padded c := by
      refine (hdec.frame_append_mem_padded_iff ?_).symm
      change Nat.card (Turing.Action k_tapes Bool State) * (c₁ * 2 ^ n ^ k + c₂) ≤
        c * (frame x ++ List.replicate (2 ^ f n) true).length
      simp only [List.length_append, length_frame, List.length_replicate]
      have hpow_le : 2 ^ n ^ k ≤ 2 ^ f n := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rcases k with _ | k <;> simp [f, h0]
        · exact (Nat.pow_le_pow_right hpos (Nat.le_succ k)).trans (Nat.le_succ _)
      have hmul : c₁ * 2 ^ n ^ k + c₂ ≤ (c₁ + c₂) * (2 * n + 1 + 2 ^ f n) := by
        have : 1 ≤ 2 * n + 1 + 2 ^ f n :=
          (Nat.le_add_left 1 (2 * n)).trans (Nat.le_add_right _ _)
        nlinarith
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hmul
    exact (hpad_iff.trans (hR_iff (z x))).trans hsearch_iff.symm
  exact hA_eq ▸ hEXP_pre

/-- **Murray–Williams Theorem 4.1 (`EXP = NEXP`, full-`NPHard` specialization)**
[Murray and Williams, Section 4.1, Theorem 4.1, p. 13][MurrayWilliams2017]:
> "If every sparse language in `NP` has a polynomial-time reduction to `MCSP`, then
> `EXP ⊂ P/poly ⟹ EXP = NEXP`."

This theorem assumes full `NPHard MCSP.encInstance MCSP` (the full-`NPHard` specialization of
Theorem 4.1) and shows that if `EXP encBits ⊆ PPolyOn encBits` then `EXP enc = NEXP enc` for every
encoding `enc` of instances. -/
theorem EXP_eq_NEXP_of_MCSP_npHard_of_EXP_subset_PPoly
    (hHard : NPHard MCSP.encInstance MCSP) (hEXP : EXP encBits ⊆ PPolyOn encBits)
    {α : Type} (enc : α ↪ List Bool) :
    EXP enc = NEXP enc :=
  EXP_subset_NEXP.antisymm (NEXP_subset_EXP_of_MCSP_npHard_of_EXP_subset_PPoly hHard hEXP enc)

/-- **Murray–Williams Theorem 1.6 (`EXP ⊈ NP ∩ P/poly`)**
[Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]:
> "If `MCSP` is `NP`-hard under polynomial-time reductions, then `EXP ≠ NP ∩ P/poly`.
> Consequently, `EXP ≠ ZPP`."

Since `NP ∩ P/poly ⊆ NP ⊆ EXP`, `EXP ≠ NP ∩ P/poly` is equivalent to
`¬ (EXP encBits ⊆ NP encBits ∩ PPolyOn encBits)`. -/
theorem not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    ¬ (EXP encBits ⊆ NP encBits ∩ PPolyOn encBits) := by
  intro h
  exact not_NEXP_subset_NP
    ((NEXP_subset_EXP_of_MCSP_npHard_of_EXP_subset_PPoly hHard (fun _ hA => (h hA).2)
      encBits).trans fun _ hA => (h hA).1)

/-- **Murray–Williams Theorem 1.6 (`EXP ≠ NP ∩ P/poly`)**
[Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]:
> "If `MCSP` is `NP`-hard under polynomial-time reductions, then `EXP ≠ NP ∩ P/poly`.
> Consequently, `EXP ≠ ZPP`." -/
theorem EXP_ne_NP_inter_PPolyOn_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    EXP encBits ≠ NP encBits ∩ PPolyOn encBits :=
  fun h => not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard hHard h.le

/-- Corollary of **Murray–Williams Theorem 1.6** (`not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard`)
[Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]: if `MCSP` is `NP`-hard
under arbitrary polynomial-time many-one reductions, then `EXP ⊈ RP`, via `RP ⊆ NP`
(`RP_subset_NP`) and `RP ⊆ BPP ⊆ P/poly` (`RP_subset_PPolyOn`). -/
theorem not_EXP_subset_RP_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    ¬ (EXP encBits ⊆ RP encBits) :=
  fun h => not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard hHard
    fun _ hA => ⟨RP_subset_NP (h hA), RP_subset_PPolyOn (h hA)⟩

/-- If `MCSP` is `NP`-hard, then `EXP ≠ RP`. -/
theorem EXP_ne_RP_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    EXP encBits ≠ RP encBits :=
  fun h => not_EXP_subset_RP_of_MCSP_npHard hHard h.le

/-- **Murray–Williams Theorem 1.6 (`EXP ⊈ ZPP`)**
[Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]: if `MCSP` is `NP`-hard,
then `EXP ⊈ ZPP`. -/
theorem not_EXP_subset_ZPP_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    ¬ (EXP encBits ⊆ ZPP encBits) :=
  fun h => not_EXP_subset_RP_of_MCSP_npHard hHard (h.trans ZPP_subset_RP)

/-- **Murray–Williams Theorem 1.6 (`EXP ≠ ZPP`)**
[Murray and Williams, Section 1, Theorem 1.6, p. 5][MurrayWilliams2017]:
> "If `MCSP` is `NP`-hard under polynomial-time reductions, then `EXP ≠ NP ∩ P/poly`.
> Consequently, `EXP ≠ ZPP`." -/
theorem EXP_ne_ZPP_of_MCSP_npHard
    (hHard : NPHard MCSP.encInstance MCSP) :
    EXP encBits ≠ ZPP encBits :=
  fun h => not_EXP_subset_ZPP_of_MCSP_npHard hHard h.le

/-- If `MCSP` is `NP`-hard and lies in `P/poly`, then `NP enc ⊆ PPolyOn enc` for every encoding
`enc` of instances. -/
theorem NP_subset_PPolyOn_of_MCSP_npHard_of_mem_PPolyOn
    (hHard : NPHard MCSP.encInstance MCSP) (hPPoly : MCSP ∈ PPolyOn MCSP.encInstance)
    {α : Type} (enc : α ↪ List Bool) :
    NP enc ⊆ PPolyOn enc :=
  fun A hA => (hHard enc A hA).mem_PPolyOn hPPoly

/-- If `MCSP` is `NP`-hard and lies in `P/poly`, then the polynomial hierarchy collapses to its
second level: `PH enc = SigmaP 2 enc` for every encoding `enc` of instances. -/
theorem PH_eq_SigmaP_two_of_MCSP_npHard_of_mem_PPolyOn
    (hHard : NPHard MCSP.encInstance MCSP) (hPPoly : MCSP ∈ PPolyOn MCSP.encInstance)
    {α : Type} (enc : α ↪ List Bool) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_NP_subset_PPoly
    fun encB => NP_subset_PPolyOn_of_MCSP_npHard_of_mem_PPolyOn hHard hPPoly encB

end Cslib.Complexity
