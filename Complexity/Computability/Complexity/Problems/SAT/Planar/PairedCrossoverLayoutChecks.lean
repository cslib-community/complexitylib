/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCrossoverLayoutData
public import Complexity.Foundations.Geometry.Orthogonal.Separation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip
import Mathlib.Tactic.FinCases

/-!
# Finite certificates for the paired-port orthogonal crossover

Finite arithmetic certificates control the full real support of every route. The core has
57 variable vertices, 78 clause vertices and 162 incidences. Eight mutually disjoint access routes
connect the signal terminals to the boundary of `[0,240]²`; only the associated terminal may meet
an access route. An external clause uses this access and the terminal's remaining occurrence.

## Main definitions

* `Cslib.Logic.PL.CNF.PairedCrossover.clausePosition`: indexed positions of clause vertices.
* `Cslib.Logic.PL.CNF.PairedCrossover.commonEndpoints`: permitted contacts of incidence routes.

## Main results

* `Cslib.Logic.PL.CNF.PairedCrossover.incidenceRoutes_cover`: exact ordinary CNF literal incidences.
* `Cslib.Logic.PL.CNF.PairedCrossover.routes_contact_check`: finite permitted-contact certificate.
* `Cslib.Logic.PL.CNF.PairedCrossover.access_contact_check`: finite access isolation certificate.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The paired modification and its finite orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedCrossover

open Orthogonal

/-- The clause position at an index. All indices in `incidenceRoutes` are certified in range. -/
def clausePosition (i : ℕ) : Point := clausePositions.getD i (0, 0)

/-- Every variable, including both lanes on each side. -/
def variableList : List Variable :=
  [.center] ++ (List.finRange 4).flatMap (fun s =>
    (List.finRange 2).map (Variable.port s)) ++
    Crossover.internalList.flatMap fun v => List.ofFn fun i : Fin 6 => Variable.copy v i

/-- Every variable is included in the finite drawing vertex list. -/
theorem mem_variableList : ∀ v, v ∈ variableList := by decide +kernel

/-- The exact literal-incidence list of the ordinary CNF formula. -/
theorem incidenceRoutes_cover :
    incidenceRoutes.map (fun e => (e.1, e.2.1)) =
      formula.zipIdx.flatMap (fun ci => ci.1.map fun l => (ci.2, l.1)) := by
  decide +kernel

/-- The fixed formula and drawing have 78 clauses and 162 incidences. -/
theorem drawing_sizes : clausePositions.length = 78 ∧ incidenceRoutes.length = 162 := by
  decide +kernel

/-- Variable vertices have distinct positions. -/
theorem variablePosition_injective : Function.Injective variablePosition := by
  have h : (variableList.map variablePosition).Nodup := by decide +kernel
  exact fun v w => List.inj_on_of_nodup_map h (mem_variableList v) (mem_variableList w)

/-- Clause vertices are pairwise distinct. -/
theorem clausePositions_nodup : clausePositions.Nodup := by decide +kernel

/-- No clause vertex is a variable vertex. -/
theorem variablePosition_not_mem_clauses :
    ∀ v, variablePosition v ∉ clausePositions := by decide +kernel

/-- The only allowed contacts between two distinct incidence routes are shared graph endpoints. -/
def commonEndpoints (e f : ℕ × Variable × Route) : List Point :=
  (if e.1 = f.1 then [clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [variablePosition e.2.1] else [])

private def LocalSpec (e : ℕ × Variable × Route) : Prop :=
  (e.1 < 78 ∧ e.2.2.head? = some (clausePosition e.1) ∧
    e.2.2.getLast? = some (variablePosition e.2.1)) ∧
  IsOrthogonal e.2.2 ∧
  (∀ p ∈ e.2.2, 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220) ∧
  e.2.2.Nodup ∧
  ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
    segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true

private instance (e : ℕ × Variable × Route) : Decidable (LocalSpec e) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def rowCheck (e : ℕ × Variable × Route) : Bool :=
  decide (LocalSpec e) &&
  ((incidenceRoutes.all fun f => e == f ||
      routeContactCheck (commonEndpoints e f) e.2.2 f.2.2) &&
   ((variableList.all fun v => v == e.2.1 ||
      routeContactCheck [] e.2.2 [variablePosition v]) &&
    ((List.finRange 78).all fun i => i.val == e.1 ||
      routeContactCheck [] e.2.2 [clausePosition i])))

private def routeAt (i : Fin 162) : ℕ × Variable × Route :=
  incidenceRoutes.getD i (0, .center, [])

-- Separate closed certificates keep kernel reduction memory bounded per incidence row.

private theorem row_0 : rowCheck (routeAt 0) = true := by decide +kernel

private theorem row_1 : rowCheck (routeAt 1) = true := by decide +kernel
private theorem row_2 : rowCheck (routeAt 2) = true := by decide +kernel
private theorem row_3 : rowCheck (routeAt 3) = true := by decide +kernel
private theorem row_4 : rowCheck (routeAt 4) = true := by decide +kernel
private theorem row_5 : rowCheck (routeAt 5) = true := by decide +kernel
private theorem row_6 : rowCheck (routeAt 6) = true := by decide +kernel
private theorem row_7 : rowCheck (routeAt 7) = true := by decide +kernel
private theorem row_8 : rowCheck (routeAt 8) = true := by decide +kernel
private theorem row_9 : rowCheck (routeAt 9) = true := by decide +kernel
private theorem row_10 : rowCheck (routeAt 10) = true := by decide +kernel

private theorem row_11 : rowCheck (routeAt 11) = true := by decide +kernel
private theorem row_12 : rowCheck (routeAt 12) = true := by decide +kernel
private theorem row_13 : rowCheck (routeAt 13) = true := by decide +kernel
private theorem row_14 : rowCheck (routeAt 14) = true := by decide +kernel
private theorem row_15 : rowCheck (routeAt 15) = true := by decide +kernel
private theorem row_16 : rowCheck (routeAt 16) = true := by decide +kernel
private theorem row_17 : rowCheck (routeAt 17) = true := by decide +kernel
private theorem row_18 : rowCheck (routeAt 18) = true := by decide +kernel
private theorem row_19 : rowCheck (routeAt 19) = true := by decide +kernel
private theorem row_20 : rowCheck (routeAt 20) = true := by decide +kernel

private theorem row_21 : rowCheck (routeAt 21) = true := by decide +kernel
private theorem row_22 : rowCheck (routeAt 22) = true := by decide +kernel
private theorem row_23 : rowCheck (routeAt 23) = true := by decide +kernel
private theorem row_24 : rowCheck (routeAt 24) = true := by decide +kernel
private theorem row_25 : rowCheck (routeAt 25) = true := by decide +kernel
private theorem row_26 : rowCheck (routeAt 26) = true := by decide +kernel
private theorem row_27 : rowCheck (routeAt 27) = true := by decide +kernel
private theorem row_28 : rowCheck (routeAt 28) = true := by decide +kernel
private theorem row_29 : rowCheck (routeAt 29) = true := by decide +kernel
private theorem row_30 : rowCheck (routeAt 30) = true := by decide +kernel

private theorem row_31 : rowCheck (routeAt 31) = true := by decide +kernel
private theorem row_32 : rowCheck (routeAt 32) = true := by decide +kernel
private theorem row_33 : rowCheck (routeAt 33) = true := by decide +kernel
private theorem row_34 : rowCheck (routeAt 34) = true := by decide +kernel
private theorem row_35 : rowCheck (routeAt 35) = true := by decide +kernel
private theorem row_36 : rowCheck (routeAt 36) = true := by decide +kernel
private theorem row_37 : rowCheck (routeAt 37) = true := by decide +kernel
private theorem row_38 : rowCheck (routeAt 38) = true := by decide +kernel
private theorem row_39 : rowCheck (routeAt 39) = true := by decide +kernel
private theorem row_40 : rowCheck (routeAt 40) = true := by decide +kernel

private theorem row_41 : rowCheck (routeAt 41) = true := by decide +kernel
private theorem row_42 : rowCheck (routeAt 42) = true := by decide +kernel
private theorem row_43 : rowCheck (routeAt 43) = true := by decide +kernel
private theorem row_44 : rowCheck (routeAt 44) = true := by decide +kernel
private theorem row_45 : rowCheck (routeAt 45) = true := by decide +kernel
private theorem row_46 : rowCheck (routeAt 46) = true := by decide +kernel
private theorem row_47 : rowCheck (routeAt 47) = true := by decide +kernel
private theorem row_48 : rowCheck (routeAt 48) = true := by decide +kernel
private theorem row_49 : rowCheck (routeAt 49) = true := by decide +kernel
private theorem row_50 : rowCheck (routeAt 50) = true := by decide +kernel

private theorem row_51 : rowCheck (routeAt 51) = true := by decide +kernel
private theorem row_52 : rowCheck (routeAt 52) = true := by decide +kernel
private theorem row_53 : rowCheck (routeAt 53) = true := by decide +kernel
private theorem row_54 : rowCheck (routeAt 54) = true := by decide +kernel
private theorem row_55 : rowCheck (routeAt 55) = true := by decide +kernel
private theorem row_56 : rowCheck (routeAt 56) = true := by decide +kernel
private theorem row_57 : rowCheck (routeAt 57) = true := by decide +kernel
private theorem row_58 : rowCheck (routeAt 58) = true := by decide +kernel
private theorem row_59 : rowCheck (routeAt 59) = true := by decide +kernel
private theorem row_60 : rowCheck (routeAt 60) = true := by decide +kernel

private theorem row_61 : rowCheck (routeAt 61) = true := by decide +kernel
private theorem row_62 : rowCheck (routeAt 62) = true := by decide +kernel
private theorem row_63 : rowCheck (routeAt 63) = true := by decide +kernel
private theorem row_64 : rowCheck (routeAt 64) = true := by decide +kernel
private theorem row_65 : rowCheck (routeAt 65) = true := by decide +kernel
private theorem row_66 : rowCheck (routeAt 66) = true := by decide +kernel
private theorem row_67 : rowCheck (routeAt 67) = true := by decide +kernel
private theorem row_68 : rowCheck (routeAt 68) = true := by decide +kernel
private theorem row_69 : rowCheck (routeAt 69) = true := by decide +kernel
private theorem row_70 : rowCheck (routeAt 70) = true := by decide +kernel

private theorem row_71 : rowCheck (routeAt 71) = true := by decide +kernel
private theorem row_72 : rowCheck (routeAt 72) = true := by decide +kernel
private theorem row_73 : rowCheck (routeAt 73) = true := by decide +kernel
private theorem row_74 : rowCheck (routeAt 74) = true := by decide +kernel
private theorem row_75 : rowCheck (routeAt 75) = true := by decide +kernel
private theorem row_76 : rowCheck (routeAt 76) = true := by decide +kernel
private theorem row_77 : rowCheck (routeAt 77) = true := by decide +kernel
private theorem row_78 : rowCheck (routeAt 78) = true := by decide +kernel
private theorem row_79 : rowCheck (routeAt 79) = true := by decide +kernel
private theorem row_80 : rowCheck (routeAt 80) = true := by decide +kernel

private theorem row_81 : rowCheck (routeAt 81) = true := by decide +kernel
private theorem row_82 : rowCheck (routeAt 82) = true := by decide +kernel
private theorem row_83 : rowCheck (routeAt 83) = true := by decide +kernel
private theorem row_84 : rowCheck (routeAt 84) = true := by decide +kernel
private theorem row_85 : rowCheck (routeAt 85) = true := by decide +kernel
private theorem row_86 : rowCheck (routeAt 86) = true := by decide +kernel
private theorem row_87 : rowCheck (routeAt 87) = true := by decide +kernel
private theorem row_88 : rowCheck (routeAt 88) = true := by decide +kernel
private theorem row_89 : rowCheck (routeAt 89) = true := by decide +kernel
private theorem row_90 : rowCheck (routeAt 90) = true := by decide +kernel

private theorem row_91 : rowCheck (routeAt 91) = true := by decide +kernel
private theorem row_92 : rowCheck (routeAt 92) = true := by decide +kernel
private theorem row_93 : rowCheck (routeAt 93) = true := by decide +kernel
private theorem row_94 : rowCheck (routeAt 94) = true := by decide +kernel
private theorem row_95 : rowCheck (routeAt 95) = true := by decide +kernel
private theorem row_96 : rowCheck (routeAt 96) = true := by decide +kernel
private theorem row_97 : rowCheck (routeAt 97) = true := by decide +kernel
private theorem row_98 : rowCheck (routeAt 98) = true := by decide +kernel
private theorem row_99 : rowCheck (routeAt 99) = true := by decide +kernel
private theorem row_100 : rowCheck (routeAt 100) = true := by decide +kernel

private theorem row_101 : rowCheck (routeAt 101) = true := by decide +kernel
private theorem row_102 : rowCheck (routeAt 102) = true := by decide +kernel
private theorem row_103 : rowCheck (routeAt 103) = true := by decide +kernel
private theorem row_104 : rowCheck (routeAt 104) = true := by decide +kernel
private theorem row_105 : rowCheck (routeAt 105) = true := by decide +kernel
private theorem row_106 : rowCheck (routeAt 106) = true := by decide +kernel
private theorem row_107 : rowCheck (routeAt 107) = true := by decide +kernel
private theorem row_108 : rowCheck (routeAt 108) = true := by decide +kernel
private theorem row_109 : rowCheck (routeAt 109) = true := by decide +kernel
private theorem row_110 : rowCheck (routeAt 110) = true := by decide +kernel

private theorem row_111 : rowCheck (routeAt 111) = true := by decide +kernel
private theorem row_112 : rowCheck (routeAt 112) = true := by decide +kernel
private theorem row_113 : rowCheck (routeAt 113) = true := by decide +kernel
private theorem row_114 : rowCheck (routeAt 114) = true := by decide +kernel
private theorem row_115 : rowCheck (routeAt 115) = true := by decide +kernel
private theorem row_116 : rowCheck (routeAt 116) = true := by decide +kernel
private theorem row_117 : rowCheck (routeAt 117) = true := by decide +kernel
private theorem row_118 : rowCheck (routeAt 118) = true := by decide +kernel
private theorem row_119 : rowCheck (routeAt 119) = true := by decide +kernel
private theorem row_120 : rowCheck (routeAt 120) = true := by decide +kernel

private theorem row_121 : rowCheck (routeAt 121) = true := by decide +kernel
private theorem row_122 : rowCheck (routeAt 122) = true := by decide +kernel
private theorem row_123 : rowCheck (routeAt 123) = true := by decide +kernel
private theorem row_124 : rowCheck (routeAt 124) = true := by decide +kernel
private theorem row_125 : rowCheck (routeAt 125) = true := by decide +kernel
private theorem row_126 : rowCheck (routeAt 126) = true := by decide +kernel
private theorem row_127 : rowCheck (routeAt 127) = true := by decide +kernel
private theorem row_128 : rowCheck (routeAt 128) = true := by decide +kernel
private theorem row_129 : rowCheck (routeAt 129) = true := by decide +kernel
private theorem row_130 : rowCheck (routeAt 130) = true := by decide +kernel

private theorem row_131 : rowCheck (routeAt 131) = true := by decide +kernel
private theorem row_132 : rowCheck (routeAt 132) = true := by decide +kernel
private theorem row_133 : rowCheck (routeAt 133) = true := by decide +kernel
private theorem row_134 : rowCheck (routeAt 134) = true := by decide +kernel
private theorem row_135 : rowCheck (routeAt 135) = true := by decide +kernel
private theorem row_136 : rowCheck (routeAt 136) = true := by decide +kernel
private theorem row_137 : rowCheck (routeAt 137) = true := by decide +kernel
private theorem row_138 : rowCheck (routeAt 138) = true := by decide +kernel
private theorem row_139 : rowCheck (routeAt 139) = true := by decide +kernel
private theorem row_140 : rowCheck (routeAt 140) = true := by decide +kernel

private theorem row_141 : rowCheck (routeAt 141) = true := by decide +kernel
private theorem row_142 : rowCheck (routeAt 142) = true := by decide +kernel
private theorem row_143 : rowCheck (routeAt 143) = true := by decide +kernel
private theorem row_144 : rowCheck (routeAt 144) = true := by decide +kernel
private theorem row_145 : rowCheck (routeAt 145) = true := by decide +kernel
private theorem row_146 : rowCheck (routeAt 146) = true := by decide +kernel
private theorem row_147 : rowCheck (routeAt 147) = true := by decide +kernel
private theorem row_148 : rowCheck (routeAt 148) = true := by decide +kernel
private theorem row_149 : rowCheck (routeAt 149) = true := by decide +kernel
private theorem row_150 : rowCheck (routeAt 150) = true := by decide +kernel

private theorem row_151 : rowCheck (routeAt 151) = true := by decide +kernel
private theorem row_152 : rowCheck (routeAt 152) = true := by decide +kernel
private theorem row_153 : rowCheck (routeAt 153) = true := by decide +kernel

private theorem row_154 : rowCheck (routeAt 154) = true := by decide +kernel
private theorem row_155 : rowCheck (routeAt 155) = true := by decide +kernel
private theorem row_156 : rowCheck (routeAt 156) = true := by decide +kernel
private theorem row_157 : rowCheck (routeAt 157) = true := by decide +kernel
private theorem row_158 : rowCheck (routeAt 158) = true := by decide +kernel
private theorem row_159 : rowCheck (routeAt 159) = true := by decide +kernel
private theorem row_160 : rowCheck (routeAt 160) = true := by decide +kernel
private theorem row_161 : rowCheck (routeAt 161) = true := by decide +kernel

-- Keep dispatch proofs small as well as the individual kernel certificates. In particular,
-- no theorem elaborates the full 162-case split: six rows form a block, then 27 blocks cover all.
private def blockIndex (q : Fin 27) (r : Fin 6) : Fin 162 :=
  ⟨q.val * 6 + r.val, by omega⟩

private theorem block_0 (r : Fin 6) : rowCheck (routeAt (blockIndex 0 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (0 : Fin 162)
    exact row_0
  · conv_lhs => arg 1; arg 1; change (1 : Fin 162)
    exact row_1
  · conv_lhs => arg 1; arg 1; change (2 : Fin 162)
    exact row_2
  · conv_lhs => arg 1; arg 1; change (3 : Fin 162)
    exact row_3
  · conv_lhs => arg 1; arg 1; change (4 : Fin 162)
    exact row_4
  · conv_lhs => arg 1; arg 1; change (5 : Fin 162)
    exact row_5

private theorem block_1 (r : Fin 6) : rowCheck (routeAt (blockIndex 1 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (6 : Fin 162)
    exact row_6
  · conv_lhs => arg 1; arg 1; change (7 : Fin 162)
    exact row_7
  · conv_lhs => arg 1; arg 1; change (8 : Fin 162)
    exact row_8
  · conv_lhs => arg 1; arg 1; change (9 : Fin 162)
    exact row_9
  · conv_lhs => arg 1; arg 1; change (10 : Fin 162)
    exact row_10
  · conv_lhs => arg 1; arg 1; change (11 : Fin 162)
    exact row_11

private theorem block_2 (r : Fin 6) : rowCheck (routeAt (blockIndex 2 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (12 : Fin 162)
    exact row_12
  · conv_lhs => arg 1; arg 1; change (13 : Fin 162)
    exact row_13
  · conv_lhs => arg 1; arg 1; change (14 : Fin 162)
    exact row_14
  · conv_lhs => arg 1; arg 1; change (15 : Fin 162)
    exact row_15
  · conv_lhs => arg 1; arg 1; change (16 : Fin 162)
    exact row_16
  · conv_lhs => arg 1; arg 1; change (17 : Fin 162)
    exact row_17

private theorem block_3 (r : Fin 6) : rowCheck (routeAt (blockIndex 3 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (18 : Fin 162)
    exact row_18
  · conv_lhs => arg 1; arg 1; change (19 : Fin 162)
    exact row_19
  · conv_lhs => arg 1; arg 1; change (20 : Fin 162)
    exact row_20
  · conv_lhs => arg 1; arg 1; change (21 : Fin 162)
    exact row_21
  · conv_lhs => arg 1; arg 1; change (22 : Fin 162)
    exact row_22
  · conv_lhs => arg 1; arg 1; change (23 : Fin 162)
    exact row_23

private theorem block_4 (r : Fin 6) : rowCheck (routeAt (blockIndex 4 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (24 : Fin 162)
    exact row_24
  · conv_lhs => arg 1; arg 1; change (25 : Fin 162)
    exact row_25
  · conv_lhs => arg 1; arg 1; change (26 : Fin 162)
    exact row_26
  · conv_lhs => arg 1; arg 1; change (27 : Fin 162)
    exact row_27
  · conv_lhs => arg 1; arg 1; change (28 : Fin 162)
    exact row_28
  · conv_lhs => arg 1; arg 1; change (29 : Fin 162)
    exact row_29

private theorem block_5 (r : Fin 6) : rowCheck (routeAt (blockIndex 5 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (30 : Fin 162)
    exact row_30
  · conv_lhs => arg 1; arg 1; change (31 : Fin 162)
    exact row_31
  · conv_lhs => arg 1; arg 1; change (32 : Fin 162)
    exact row_32
  · conv_lhs => arg 1; arg 1; change (33 : Fin 162)
    exact row_33
  · conv_lhs => arg 1; arg 1; change (34 : Fin 162)
    exact row_34
  · conv_lhs => arg 1; arg 1; change (35 : Fin 162)
    exact row_35

private theorem block_6 (r : Fin 6) : rowCheck (routeAt (blockIndex 6 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (36 : Fin 162)
    exact row_36
  · conv_lhs => arg 1; arg 1; change (37 : Fin 162)
    exact row_37
  · conv_lhs => arg 1; arg 1; change (38 : Fin 162)
    exact row_38
  · conv_lhs => arg 1; arg 1; change (39 : Fin 162)
    exact row_39
  · conv_lhs => arg 1; arg 1; change (40 : Fin 162)
    exact row_40
  · conv_lhs => arg 1; arg 1; change (41 : Fin 162)
    exact row_41

private theorem block_7 (r : Fin 6) : rowCheck (routeAt (blockIndex 7 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (42 : Fin 162)
    exact row_42
  · conv_lhs => arg 1; arg 1; change (43 : Fin 162)
    exact row_43
  · conv_lhs => arg 1; arg 1; change (44 : Fin 162)
    exact row_44
  · conv_lhs => arg 1; arg 1; change (45 : Fin 162)
    exact row_45
  · conv_lhs => arg 1; arg 1; change (46 : Fin 162)
    exact row_46
  · conv_lhs => arg 1; arg 1; change (47 : Fin 162)
    exact row_47

private theorem block_8 (r : Fin 6) : rowCheck (routeAt (blockIndex 8 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (48 : Fin 162)
    exact row_48
  · conv_lhs => arg 1; arg 1; change (49 : Fin 162)
    exact row_49
  · conv_lhs => arg 1; arg 1; change (50 : Fin 162)
    exact row_50
  · conv_lhs => arg 1; arg 1; change (51 : Fin 162)
    exact row_51
  · conv_lhs => arg 1; arg 1; change (52 : Fin 162)
    exact row_52
  · conv_lhs => arg 1; arg 1; change (53 : Fin 162)
    exact row_53

private theorem block_9 (r : Fin 6) : rowCheck (routeAt (blockIndex 9 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (54 : Fin 162)
    exact row_54
  · conv_lhs => arg 1; arg 1; change (55 : Fin 162)
    exact row_55
  · conv_lhs => arg 1; arg 1; change (56 : Fin 162)
    exact row_56
  · conv_lhs => arg 1; arg 1; change (57 : Fin 162)
    exact row_57
  · conv_lhs => arg 1; arg 1; change (58 : Fin 162)
    exact row_58
  · conv_lhs => arg 1; arg 1; change (59 : Fin 162)
    exact row_59

private theorem block_10 (r : Fin 6) : rowCheck (routeAt (blockIndex 10 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (60 : Fin 162)
    exact row_60
  · conv_lhs => arg 1; arg 1; change (61 : Fin 162)
    exact row_61
  · conv_lhs => arg 1; arg 1; change (62 : Fin 162)
    exact row_62
  · conv_lhs => arg 1; arg 1; change (63 : Fin 162)
    exact row_63
  · conv_lhs => arg 1; arg 1; change (64 : Fin 162)
    exact row_64
  · conv_lhs => arg 1; arg 1; change (65 : Fin 162)
    exact row_65

private theorem block_11 (r : Fin 6) : rowCheck (routeAt (blockIndex 11 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (66 : Fin 162)
    exact row_66
  · conv_lhs => arg 1; arg 1; change (67 : Fin 162)
    exact row_67
  · conv_lhs => arg 1; arg 1; change (68 : Fin 162)
    exact row_68
  · conv_lhs => arg 1; arg 1; change (69 : Fin 162)
    exact row_69
  · conv_lhs => arg 1; arg 1; change (70 : Fin 162)
    exact row_70
  · conv_lhs => arg 1; arg 1; change (71 : Fin 162)
    exact row_71

private theorem block_12 (r : Fin 6) : rowCheck (routeAt (blockIndex 12 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (72 : Fin 162)
    exact row_72
  · conv_lhs => arg 1; arg 1; change (73 : Fin 162)
    exact row_73
  · conv_lhs => arg 1; arg 1; change (74 : Fin 162)
    exact row_74
  · conv_lhs => arg 1; arg 1; change (75 : Fin 162)
    exact row_75
  · conv_lhs => arg 1; arg 1; change (76 : Fin 162)
    exact row_76
  · conv_lhs => arg 1; arg 1; change (77 : Fin 162)
    exact row_77

private theorem block_13 (r : Fin 6) : rowCheck (routeAt (blockIndex 13 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (78 : Fin 162)
    exact row_78
  · conv_lhs => arg 1; arg 1; change (79 : Fin 162)
    exact row_79
  · conv_lhs => arg 1; arg 1; change (80 : Fin 162)
    exact row_80
  · conv_lhs => arg 1; arg 1; change (81 : Fin 162)
    exact row_81
  · conv_lhs => arg 1; arg 1; change (82 : Fin 162)
    exact row_82
  · conv_lhs => arg 1; arg 1; change (83 : Fin 162)
    exact row_83

private theorem block_14 (r : Fin 6) : rowCheck (routeAt (blockIndex 14 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (84 : Fin 162)
    exact row_84
  · conv_lhs => arg 1; arg 1; change (85 : Fin 162)
    exact row_85
  · conv_lhs => arg 1; arg 1; change (86 : Fin 162)
    exact row_86
  · conv_lhs => arg 1; arg 1; change (87 : Fin 162)
    exact row_87
  · conv_lhs => arg 1; arg 1; change (88 : Fin 162)
    exact row_88
  · conv_lhs => arg 1; arg 1; change (89 : Fin 162)
    exact row_89

private theorem block_15 (r : Fin 6) : rowCheck (routeAt (blockIndex 15 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (90 : Fin 162)
    exact row_90
  · conv_lhs => arg 1; arg 1; change (91 : Fin 162)
    exact row_91
  · conv_lhs => arg 1; arg 1; change (92 : Fin 162)
    exact row_92
  · conv_lhs => arg 1; arg 1; change (93 : Fin 162)
    exact row_93
  · conv_lhs => arg 1; arg 1; change (94 : Fin 162)
    exact row_94
  · conv_lhs => arg 1; arg 1; change (95 : Fin 162)
    exact row_95

private theorem block_16 (r : Fin 6) : rowCheck (routeAt (blockIndex 16 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (96 : Fin 162)
    exact row_96
  · conv_lhs => arg 1; arg 1; change (97 : Fin 162)
    exact row_97
  · conv_lhs => arg 1; arg 1; change (98 : Fin 162)
    exact row_98
  · conv_lhs => arg 1; arg 1; change (99 : Fin 162)
    exact row_99
  · conv_lhs => arg 1; arg 1; change (100 : Fin 162)
    exact row_100
  · conv_lhs => arg 1; arg 1; change (101 : Fin 162)
    exact row_101

private theorem block_17 (r : Fin 6) : rowCheck (routeAt (blockIndex 17 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (102 : Fin 162)
    exact row_102
  · conv_lhs => arg 1; arg 1; change (103 : Fin 162)
    exact row_103
  · conv_lhs => arg 1; arg 1; change (104 : Fin 162)
    exact row_104
  · conv_lhs => arg 1; arg 1; change (105 : Fin 162)
    exact row_105
  · conv_lhs => arg 1; arg 1; change (106 : Fin 162)
    exact row_106
  · conv_lhs => arg 1; arg 1; change (107 : Fin 162)
    exact row_107

private theorem block_18 (r : Fin 6) : rowCheck (routeAt (blockIndex 18 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (108 : Fin 162)
    exact row_108
  · conv_lhs => arg 1; arg 1; change (109 : Fin 162)
    exact row_109
  · conv_lhs => arg 1; arg 1; change (110 : Fin 162)
    exact row_110
  · conv_lhs => arg 1; arg 1; change (111 : Fin 162)
    exact row_111
  · conv_lhs => arg 1; arg 1; change (112 : Fin 162)
    exact row_112
  · conv_lhs => arg 1; arg 1; change (113 : Fin 162)
    exact row_113

private theorem block_19 (r : Fin 6) : rowCheck (routeAt (blockIndex 19 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (114 : Fin 162)
    exact row_114
  · conv_lhs => arg 1; arg 1; change (115 : Fin 162)
    exact row_115
  · conv_lhs => arg 1; arg 1; change (116 : Fin 162)
    exact row_116
  · conv_lhs => arg 1; arg 1; change (117 : Fin 162)
    exact row_117
  · conv_lhs => arg 1; arg 1; change (118 : Fin 162)
    exact row_118
  · conv_lhs => arg 1; arg 1; change (119 : Fin 162)
    exact row_119

private theorem block_20 (r : Fin 6) : rowCheck (routeAt (blockIndex 20 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (120 : Fin 162)
    exact row_120
  · conv_lhs => arg 1; arg 1; change (121 : Fin 162)
    exact row_121
  · conv_lhs => arg 1; arg 1; change (122 : Fin 162)
    exact row_122
  · conv_lhs => arg 1; arg 1; change (123 : Fin 162)
    exact row_123
  · conv_lhs => arg 1; arg 1; change (124 : Fin 162)
    exact row_124
  · conv_lhs => arg 1; arg 1; change (125 : Fin 162)
    exact row_125

private theorem block_21 (r : Fin 6) : rowCheck (routeAt (blockIndex 21 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (126 : Fin 162)
    exact row_126
  · conv_lhs => arg 1; arg 1; change (127 : Fin 162)
    exact row_127
  · conv_lhs => arg 1; arg 1; change (128 : Fin 162)
    exact row_128
  · conv_lhs => arg 1; arg 1; change (129 : Fin 162)
    exact row_129
  · conv_lhs => arg 1; arg 1; change (130 : Fin 162)
    exact row_130
  · conv_lhs => arg 1; arg 1; change (131 : Fin 162)
    exact row_131

private theorem block_22 (r : Fin 6) : rowCheck (routeAt (blockIndex 22 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (132 : Fin 162)
    exact row_132
  · conv_lhs => arg 1; arg 1; change (133 : Fin 162)
    exact row_133
  · conv_lhs => arg 1; arg 1; change (134 : Fin 162)
    exact row_134
  · conv_lhs => arg 1; arg 1; change (135 : Fin 162)
    exact row_135
  · conv_lhs => arg 1; arg 1; change (136 : Fin 162)
    exact row_136
  · conv_lhs => arg 1; arg 1; change (137 : Fin 162)
    exact row_137

private theorem block_23 (r : Fin 6) : rowCheck (routeAt (blockIndex 23 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (138 : Fin 162)
    exact row_138
  · conv_lhs => arg 1; arg 1; change (139 : Fin 162)
    exact row_139
  · conv_lhs => arg 1; arg 1; change (140 : Fin 162)
    exact row_140
  · conv_lhs => arg 1; arg 1; change (141 : Fin 162)
    exact row_141
  · conv_lhs => arg 1; arg 1; change (142 : Fin 162)
    exact row_142
  · conv_lhs => arg 1; arg 1; change (143 : Fin 162)
    exact row_143

private theorem block_24 (r : Fin 6) : rowCheck (routeAt (blockIndex 24 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (144 : Fin 162)
    exact row_144
  · conv_lhs => arg 1; arg 1; change (145 : Fin 162)
    exact row_145
  · conv_lhs => arg 1; arg 1; change (146 : Fin 162)
    exact row_146
  · conv_lhs => arg 1; arg 1; change (147 : Fin 162)
    exact row_147
  · conv_lhs => arg 1; arg 1; change (148 : Fin 162)
    exact row_148
  · conv_lhs => arg 1; arg 1; change (149 : Fin 162)
    exact row_149

private theorem block_25 (r : Fin 6) : rowCheck (routeAt (blockIndex 25 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (150 : Fin 162)
    exact row_150
  · conv_lhs => arg 1; arg 1; change (151 : Fin 162)
    exact row_151
  · conv_lhs => arg 1; arg 1; change (152 : Fin 162)
    exact row_152
  · conv_lhs => arg 1; arg 1; change (153 : Fin 162)
    exact row_153
  · conv_lhs => arg 1; arg 1; change (154 : Fin 162)
    exact row_154
  · conv_lhs => arg 1; arg 1; change (155 : Fin 162)
    exact row_155

private theorem block_26 (r : Fin 6) : rowCheck (routeAt (blockIndex 26 r)) = true := by
  fin_cases r
  · conv_lhs => arg 1; arg 1; change (156 : Fin 162)
    exact row_156
  · conv_lhs => arg 1; arg 1; change (157 : Fin 162)
    exact row_157
  · conv_lhs => arg 1; arg 1; change (158 : Fin 162)
    exact row_158
  · conv_lhs => arg 1; arg 1; change (159 : Fin 162)
    exact row_159
  · conv_lhs => arg 1; arg 1; change (160 : Fin 162)
    exact row_160
  · conv_lhs => arg 1; arg 1; change (161 : Fin 162)
    exact row_161

private theorem blocks_checked (q : Fin 27) (r : Fin 6) :
    rowCheck (routeAt (blockIndex q r)) = true := by
  fin_cases q
  · exact block_0 r
  · exact block_1 r
  · exact block_2 r
  · exact block_3 r
  · exact block_4 r
  · exact block_5 r
  · exact block_6 r
  · exact block_7 r
  · exact block_8 r
  · exact block_9 r
  · exact block_10 r
  · exact block_11 r
  · exact block_12 r
  · exact block_13 r
  · exact block_14 r
  · exact block_15 r
  · exact block_16 r
  · exact block_17 r
  · exact block_18 r
  · exact block_19 r
  · exact block_20 r
  · exact block_21 r
  · exact block_22 r
  · exact block_23 r
  · exact block_24 r
  · exact block_25 r
  · exact block_26 r

private theorem rows_checked (i : Fin 162) : rowCheck (routeAt i) = true := by
  let q : Fin 27 := ⟨i.val / 6, by omega⟩
  let r : Fin 6 := ⟨i.val % 6, by omega⟩
  have heq : blockIndex q r = i := by
    apply Fin.ext
    simp only [blockIndex, q, r]
    omega
  have h := blocks_checked q r
  rwa [heq] at h

private theorem row_checked (e : ℕ × Variable × Route) (he : e ∈ incidenceRoutes) :
    rowCheck e = true := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
  have hi : i.val < 162 := by simpa only [drawing_sizes.2] using i.isLt
  have h := rows_checked ⟨i.val, hi⟩
  have heq : routeAt ⟨i.val, hi⟩ = incidenceRoutes.get i :=
    List.getD_eq_get incidenceRoutes (0, .center, []) i
  rwa [heq] at h

private theorem local_checked (e : ℕ × Variable × Route) (he : e ∈ incidenceRoutes) :
    LocalSpec e := by
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every route starts at its clause and ends at its variable, with a valid clause index. -/
theorem incidence_endpoints : ∀ e ∈ incidenceRoutes,
    e.1 < 78 ∧ e.2.2.head? = some (clausePosition e.1) ∧
      e.2.2.getLast? = some (variablePosition e.2.1) :=
  fun e he => (local_checked e he).1

/-- All incidence routes have proper axis-aligned segments. -/
theorem incidence_orthogonal :
    ∀ e ∈ incidenceRoutes, IsOrthogonal e.2.2 :=
  fun e he => (local_checked e he).2.1

/-- All listed core points are inside the smaller rectangle `[20,220]²`. -/
theorem core_bounds : ∀ e ∈ incidenceRoutes, ∀ p ∈ e.2.2,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 :=
  fun e he => (local_checked e he).2.2.1

/-- Exactly 407 proper segments and 2192 units of total Manhattan wire length. -/
theorem route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum = 407 ∧
      (incidenceRoutes.map fun e => wireLength e.2.2).sum = 2192 := by decide +kernel

/-- Every incidence route lists each bend only once. -/
theorem incidence_points_nodup : ∀ e ∈ incidenceRoutes, e.2.2.Nodup :=
  fun e he => (local_checked e he).2.2.2.1

/-- Finite simplicity certificate: distinct segments are disjoint except at a shared next bend. -/
theorem incidence_simple_check : ∀ e ∈ incidenceRoutes,
    ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
      segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true :=
  fun e he => (local_checked e he).2.2.2.2

/-- Exhaustive finite contact certificate for the fixed route table. -/
theorem routes_contact_check : ∀ e ∈ incidenceRoutes, ∀ f ∈ incidenceRoutes,
    e ≠ f → routeContactCheck (commonEndpoints e f) e.2.2 f.2.2 = true := by
  intro e he f hf hne
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hf' := List.all_eq_true.mp h.2.1 f hf
  simpa only [Bool.or_eq_true, beq_iff_eq, hne, false_or] using hf'

/-- No route visits a nonincident variable vertex. -/
theorem variable_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ v,
    v ≠ e.2.1 → routeContactCheck [] e.2.2 [variablePosition v] = true := by
  intro e he v hv
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hv' := List.all_eq_true.mp h.2.2.1 v (mem_variableList v)
  simpa only [Bool.or_eq_true, beq_iff_eq, hv, false_or] using hv'

/-- No route visits a nonincident clause vertex. -/
theorem clause_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ i : Fin 78,
    i.val ≠ e.1 → routeContactCheck [] e.2.2 [clausePosition i] = true := by
  intro e he i hi
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hi' := List.all_eq_true.mp h.2.2.2 i (List.mem_finRange i)
  simpa only [Bool.or_eq_true, beq_iff_eq, hi, false_or] using hi'

/-- All eight access routes have their prescribed endpoints and proper orthogonal segments. -/
theorem access_endpoints : ∀ s l, IsOrthogonal (accessRoute s l) ∧
    (accessRoute s l).head? = some (boundaryPort s l) ∧
      (accessRoute s l).getLast? = some (variablePosition (terminal s l)) := by decide +kernel

/-- The eight access routes are mutually disjoint. -/
theorem access_disjoint_check : ∀ p q : PairedPorts.Port, p ≠ q →
    routeContactCheck [] (accessRoute p.1 p.2) (accessRoute q.1 q.2) = true :=
  PairedPorts.access_disjoint_check

/-- Access to a port can meet an incidence route only at that port. -/
theorem access_contact_check : ∀ s l, ∀ e ∈ incidenceRoutes,
    routeContactCheck (if e.2.1 = terminal s l then [variablePosition (terminal s l)] else [])
      (accessRoute s l) e.2.2 = true := by decide +kernel

end Cslib.Logic.PL.CNF.PairedCrossover
