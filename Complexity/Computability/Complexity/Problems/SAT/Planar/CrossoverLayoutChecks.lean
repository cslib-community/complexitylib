/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.CrossoverLayoutData
public import Complexity.Foundations.Geometry.Orthogonal.Separation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Zip
import Mathlib.Tactic.FinCases

/-!
# Finite certificates for the fixed orthogonal crossover

Finite arithmetic certificates control the full real support of every route. The core has
53 variable vertices, 74 clause vertices and 154 incidences. Four mutually disjoint access routes
connect the signal terminals to the boundary of `[0,240]²`; only the associated terminal may meet
an access route. An external clause uses this access and the terminal's remaining occurrence.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.clausePosition`: indexed positions of clause vertices.
* `Cslib.Logic.PL.CNF.Crossover.commonEndpoints`: permitted contacts of incidence routes.

## Main results

* `Cslib.Logic.PL.CNF.Crossover.incidenceRoutes_cover`: exact ordinary CNF literal incidences.
* `Cslib.Logic.PL.CNF.Crossover.routes_contact_check`: finite permitted-contact certificate.
* `Cslib.Logic.PL.CNF.Crossover.access_contact_check`: finite access isolation certificate.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The finite orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

open Orthogonal

/-- The clause position at an index. All indices in `incidenceRoutes` are certified in range. -/
def clausePosition (i : ℕ) : Point := clausePositions.getD i (0, 0)

/-- All variable names, with each local six-copy block listed in order. -/
def splitVariables : List SplitVariable :=
  [.aLeft, .aRight, .bTop, .bBottom, .center] ++
    internalList.flatMap fun v => List.ofFn fun i : Fin 6 => SplitVariable.copy v i

/-- Every variable name is included in the explicit finite vertex list. -/
theorem mem_splitVariables (v : SplitVariable) : v ∈ splitVariables := by
  cases v with
  | aLeft | aRight | bTop | bBottom | center => decide
  | copy v i =>
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨v, mem_internalList v, List.mem_ofFn.mpr ⟨i, rfl⟩⟩

/-- The exact literal-incidence list of the ordinary CNF formula. -/
theorem incidenceRoutes_cover :
    incidenceRoutes.map (fun e => (e.1, e.2.1)) =
      splitFormula.zipIdx.flatMap (fun ci => ci.1.map fun l => (ci.2, l.1)) := by
  decide +kernel

/-- The fixed formula and drawing have 74 clauses and 154 incidences. -/
theorem drawing_sizes : clausePositions.length = 74 ∧ incidenceRoutes.length = 154 := by
  decide +kernel

/-- Variable vertices have distinct positions. -/
theorem variablePosition_injective : Function.Injective variablePosition := by
  have h : (splitVariables.map variablePosition).Nodup := by decide +kernel
  exact fun v w => List.inj_on_of_nodup_map h (mem_splitVariables v) (mem_splitVariables w)

/-- Clause vertices are pairwise distinct. -/
theorem clausePositions_nodup : clausePositions.Nodup := by decide +kernel

/-- No clause vertex is a variable vertex. -/
theorem variablePosition_not_mem_clauses :
    ∀ v, variablePosition v ∉ clausePositions := by decide +kernel

/-- The only allowed contacts between two distinct incidence routes are shared graph endpoints. -/
def commonEndpoints (e f : ℕ × SplitVariable × Route) : List Point :=
  (if e.1 = f.1 then [clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [variablePosition e.2.1] else [])

private def LocalSpec (e : ℕ × SplitVariable × Route) : Prop :=
  (e.1 < 74 ∧ e.2.2.head? = some (clausePosition e.1) ∧
    e.2.2.getLast? = some (variablePosition e.2.1)) ∧
  IsOrthogonal e.2.2 ∧
  (∀ p ∈ e.2.2, 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220) ∧
  e.2.2.Nodup ∧
  ∀ a ∈ e.2.2.consecutivePairs, ∀ b ∈ e.2.2.consecutivePairs, a ≠ b →
    segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true

private instance (e : ℕ × SplitVariable × Route) : Decidable (LocalSpec e) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def rowCheck (e : ℕ × SplitVariable × Route) : Bool :=
  decide (LocalSpec e) &&
  ((incidenceRoutes.all fun f => e == f ||
      routeContactCheck (commonEndpoints e f) e.2.2 f.2.2) &&
   ((splitVariables.all fun v => v == e.2.1 ||
      routeContactCheck [] e.2.2 [variablePosition v]) &&
    ((List.finRange 74).all fun i => i.val == e.1 ||
      routeContactCheck [] e.2.2 [clausePosition i])))

private def routeAt (i : Fin 154) : ℕ × SplitVariable × Route :=
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

private theorem rows_checked (i : Fin 154) : rowCheck (routeAt i) = true := by
  fin_cases i
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
  · exact row_64
  · exact row_65
  · exact row_66
  · exact row_67
  · exact row_68
  · exact row_69
  · exact row_70
  · exact row_71
  · exact row_72
  · exact row_73
  · exact row_74
  · exact row_75
  · exact row_76
  · exact row_77
  · exact row_78
  · exact row_79
  · exact row_80
  · exact row_81
  · exact row_82
  · exact row_83
  · exact row_84
  · exact row_85
  · exact row_86
  · exact row_87
  · exact row_88
  · exact row_89
  · exact row_90
  · exact row_91
  · exact row_92
  · exact row_93
  · exact row_94
  · exact row_95
  · exact row_96
  · exact row_97
  · exact row_98
  · exact row_99
  · exact row_100
  · exact row_101
  · exact row_102
  · exact row_103
  · exact row_104
  · exact row_105
  · exact row_106
  · exact row_107
  · exact row_108
  · exact row_109
  · exact row_110
  · exact row_111
  · exact row_112
  · exact row_113
  · exact row_114
  · exact row_115
  · exact row_116
  · exact row_117
  · exact row_118
  · exact row_119
  · exact row_120
  · exact row_121
  · exact row_122
  · exact row_123
  · exact row_124
  · exact row_125
  · exact row_126
  · exact row_127
  · exact row_128
  · exact row_129
  · exact row_130
  · exact row_131
  · exact row_132
  · exact row_133
  · exact row_134
  · exact row_135
  · exact row_136
  · exact row_137
  · exact row_138
  · exact row_139
  · exact row_140
  · exact row_141
  · exact row_142
  · exact row_143
  · exact row_144
  · exact row_145
  · exact row_146
  · exact row_147
  · exact row_148
  · exact row_149
  · exact row_150
  · exact row_151
  · exact row_152
  · exact row_153

private theorem row_checked (e : ℕ × SplitVariable × Route) (he : e ∈ incidenceRoutes) :
    rowCheck e = true := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
  have hi : i.val < 154 := by simpa only [drawing_sizes.2] using i.isLt
  have h := rows_checked ⟨i.val, hi⟩
  have heq : routeAt ⟨i.val, hi⟩ = incidenceRoutes.get i :=
    List.getD_eq_get incidenceRoutes (0, .center, []) i
  rwa [heq] at h

private theorem local_checked (e : ℕ × SplitVariable × Route) (he : e ∈ incidenceRoutes) :
    LocalSpec e := by
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every route starts at its clause and ends at its variable, with a valid clause index. -/
theorem incidence_endpoints : ∀ e ∈ incidenceRoutes,
    e.1 < 74 ∧ e.2.2.head? = some (clausePosition e.1) ∧
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

/-- Exactly 410 proper segments and 2116 units of total Manhattan wire length. -/
theorem route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum = 410 ∧
      (incidenceRoutes.map fun e => wireLength e.2.2).sum = 2116 := by decide +kernel

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
  have hv' := List.all_eq_true.mp h.2.2.1 v (mem_splitVariables v)
  simpa only [Bool.or_eq_true, beq_iff_eq, hv, false_or] using hv'

/-- No route visits a nonincident clause vertex. -/
theorem clause_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ i : Fin 74,
    i.val ≠ e.1 → routeContactCheck [] e.2.2 [clausePosition i] = true := by
  intro e he i hi
  have h := row_checked e he
  simp only [rowCheck, Bool.and_eq_true] at h
  have hi' := List.all_eq_true.mp h.2.2.2 i (List.mem_finRange i)
  simpa only [Bool.or_eq_true, beq_iff_eq, hi, false_or] using hi'

/-- Four simple orthogonal access routes, each with its prescribed endpoints. -/
theorem access_endpoints : ∀ i, IsOrthogonal (accessRoute i) ∧
    (accessRoute i).head? = some (boundaryPort i) ∧
      (accessRoute i).getLast? = some (variablePosition (splitTerminal i)) := by decide +kernel

/-- The four access routes are mutually disjoint. -/
theorem access_disjoint_check : ∀ i j, i ≠ j →
    routeContactCheck [] (accessRoute i) (accessRoute j) = true := by decide +kernel

/-- Access to a terminal can meet an incidence route only at that terminal. -/
theorem access_contact_check : ∀ i, ∀ e ∈ incidenceRoutes,
    routeContactCheck (if e.2.1 = splitTerminal i then [variablePosition (splitTerminal i)] else [])
      (accessRoute i) e.2.2 = true := by decide +kernel

end Cslib.Logic.PL.CNF.Crossover
