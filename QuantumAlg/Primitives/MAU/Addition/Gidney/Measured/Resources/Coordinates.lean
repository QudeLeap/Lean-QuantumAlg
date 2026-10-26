/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Coordinates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail

/-!
# Closed native CNOT and paid one-qubit bounds of the actual measured adder

Both complements pay every native X. Both stored-record phase passes pay
their possible Z, and each physical vent pays H and its possible reset X.
The CNOT bound sums the original stream and carry repair generators
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma native_cnot {records : Nat} (gates : List (GateSpec encoding)) :
    wordCnotCount (records := records) [.native gates] =
      (gates.map cnotMultiplicity).sum := by
  simp only [wordCnotCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    cnotCount, Nat.add_zero]

private lemma native_single {records : Nat} (gates : List (GateSpec encoding)) :
    wordSingleQubitBound (records := records) [.native gates] =
      (gates.map xMultiplicity).sum := by
  simp only [wordSingleQubitBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    singleQubitBound, Nat.add_zero]

private lemma complement_cnot (layout : Layout encoding width) :
    (layout.complementGates.map cnotMultiplicity).sum = 0 := by
  simp only [complementGates, List.map_ofFn, Function.comp_def, cnotMultiplicity,
    List.sum_ofFn, Finset.sum_const_zero]

private lemma complement_single (layout : Layout encoding width) :
    (layout.complementGates.map xMultiplicity).sum = width := by
  simp [complementGates, List.map_ofFn, Function.comp_def, xMultiplicity]

private lemma phase_cnot (layout : Layout encoding width) :
    wordCnotCount layout.phaseWord = 0 := by
  simp only [wordCnotCount, phaseWord, List.map_ofFn, Function.comp_def, cnotCount,
    List.sum_ofFn, Finset.sum_const_zero]

private lemma phase_single (layout : Layout encoding width) :
    wordSingleQubitBound layout.phaseWord = width - 2 := by
  simp [wordSingleQubitBound, phaseWord, List.map_ofFn, Function.comp_def,
    singleQubitBound]

/-- Actual CNOT occurrences have the width bound obtained from the two literal generators. -/
lemma adderWord_cnot_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (constant : BitVec width) :
    wordCnotCount (layout.adderWord wide constant) ≤ 13 * width - 27 := by
  rw [adderWord_eq_stream_tail]
  simp only [tailWord, wordCnotCount_append, native_cnot, complement_cnot,
    phase_cnot, Nat.zero_add, Nat.add_zero]
  have stream := streamingWord_cnot_bound layout wide constant
  have carry := CarryLayout.gates_cnot_bound layout.carryLayout (constant.setWidth (width - 2))
  omega

/-- H/reset/Z and complements pay six one-qubit instructions per bit minus eight. -/
lemma adderWord_single_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordSingleQubitBound (layout.adderWord wide constant) = 6 * width - 8 := by
  rw [adderWord_eq_stream_tail]
  simp only [tailWord, wordSingleQubitBound_append, native_single, complement_single,
    phase_single, CarryLayout.gates_x_count, Nat.add_zero,
    streamingWord_single_bound layout wide constant]
  omega

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
