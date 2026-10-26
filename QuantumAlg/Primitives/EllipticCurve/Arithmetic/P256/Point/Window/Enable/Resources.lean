/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Counts
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Exact emitted native resources of both whole-digit enable directions -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open QuantumAlg.EncodedBit

variable {Data : Type} {dataEncoding : BinaryLabelEncoding Data} {controls : Nat}

lemma toggleGates_native_counts (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (enough : 2 ≤ controls) :
    ((toggleGates ports).map GateSpec.toffoliMultiplicity).sum =
        Word.OneDirtyLayout.gateCount controls ∧
      ((toggleGates ports).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((toggleGates ports).map GateSpec.xMultiplicity).sum = 2 * controls + 1 := by
  have actual := ports.patternGates_native_counts enough (fun _ => false)
  have masks : (Word.OneDirtyLayout.patternMaskIndices (fun _ : Fin controls => false)).length =
      controls := by simp [Word.OneDirtyLayout.patternMaskIndices]
  rw [masks] at actual
  refine ⟨?_, ?_, ?_⟩
  · simpa only [toggleGates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, GateSpec.toffoliMultiplicity, Nat.zero_add] using actual.1
  · simpa only [toggleGates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, GateSpec.cnotMultiplicity, Nat.zero_add] using actual.2.1
  · simp only [toggleGates, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, GateSpec.xMultiplicity, Nat.add_zero, actual.2.2]
    omega

lemma toggleGates_length (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls) :
    (toggleGates ports).length = 2 * controls + Word.OneDirtyLayout.gateCount controls + 1 := by
  rw [toggleGates, List.length_append, List.length_singleton,
    Word.OneDirtyLayout.patternGates_length, Word.OneDirtyLayout.gates_length]
  simp only [Word.OneDirtyLayout.patternMaskIndices, Bool.not_false, List.filter_true,
    List.length_ofFn]
  omega

lemma program_native_counts (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program stream width bounded).eventCost = Word.OneDirtyLayout.gateCount (width + 1) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program stream width bounded).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program stream width bounded).eventCost =
        2 * (width + 1) + 1 := by
  simpa only [program, gates, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_x_count_eq_sum] using
      toggleGates_native_counts (layout stream width bounded) (by omega)

lemma inverseProgram_count (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (inverseProgram stream width bounded).eventCost =
      ResourcePool.count focus (program stream width bounded).eventCost := by
  simp only [inverseProgram, program, GateSpec.programList_eventCost,
    ResourcePool.count_ofList, List.map_reverse, List.count_reverse]

lemma program_quantumTime (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    (program stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 1 :=
  (GateSpec.programList_quantumTime (QubitLayout.canonical _) .empty _).trans
    (toggleGates_length (layout stream width bounded))

lemma inverseProgram_quantumTime (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    (inverseProgram stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 1 :=
  (GateSpec.programList_quantumTime (QubitLayout.canonical _) .empty _).trans
    ((List.length_reverse (as := gates stream width bounded)).trans
      (toggleGates_length (layout stream width bounded)))

lemma full_native_counts (stream : Fin 2) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program stream 15 (by omega)).eventCost = 104 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program stream 15 (by omega)).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program stream 15 (by omega)).eventCost = 33 :=
  program_native_counts stream 15 (by omega) (by omega)

lemma tail_native_counts (stream : Fin 2) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program stream 3 (by omega)).eventCost = 10 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program stream 3 (by omega)).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program stream 3 (by omega)).eventCost = 9 :=
  program_native_counts stream 3 (by omega) (by omega)

lemma full_quantumTime (stream : Fin 2) :
    (program stream 15 (by omega)).evaluatedEventDepth Resource.Event.quantumDuration = 137 :=
  program_quantumTime stream 15 (by omega)

lemma tail_quantumTime (stream : Fin 2) :
    (program stream 3 (by omega)).evaluatedEventDepth Resource.Event.quantumDuration = 19 :=
  program_quantumTime stream 3 (by omega)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
