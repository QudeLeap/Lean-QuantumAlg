/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Control
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Resources

/-! # Paid native coordinates of both F-to-N control-transfer directions -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Control

noncomputable section

open QuantumAlg.EncodedBit GateSpec Window

lemma prepareProgram_native_counts (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (prepareProgram stream width bounded).eventCost =
        Word.OneDirtyLayout.gateCount (width + 1) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (prepareProgram stream width bounded).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (prepareProgram stream width bounded).eventCost = 2 * (width + 1) + 1 := by
  have actual := Enable.toggleGates_native_counts (Enable.layout stream width bounded)
    (by omega)
  have paid := And.intro actual.1 (And.intro
    (congrArg (fun amount => 1 + amount) actual.2.1) actual.2.2)
  simpa only [prepareProgram, programList_toffoli_count_eq_sum,
    programList_cnot_count_eq_sum, programList_x_count_eq_sum, prepareGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.map_reverse, List.sum_reverse, copyGate, toffoliMultiplicity, cnotMultiplicity,
    xMultiplicity, Nat.zero_add, Nat.add_zero, Enable.gates] using paid

lemma restoreProgram_count (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (restoreProgram stream width bounded).eventCost =
      ResourcePool.count focus (prepareProgram stream width bounded).eventCost := by
  simp only [restoreProgram, prepareProgram, programList_eventCost, ResourcePool.count_ofList,
    restoreGates, prepareGates, List.map_append, List.count_append, List.map_reverse,
    List.count_reverse]
  exact Nat.add_comm _ _

lemma prepareProgram_quantumTime (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    (prepareProgram stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 2 := by
  have count : (Enable.gates stream width bounded).length =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 1 :=
    Enable.toggleGates_length (Enable.layout stream width bounded)
  have duration :
      (prepareProgram stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
        (prepareGates stream width bounded).length :=
    programList_quantumTime (encoding := Window.encoding)
      (QubitLayout.canonical Window.encoding.width) OracleModel.empty
      (prepareGates stream width bounded)
  rw [duration, prepareGates, List.length_append,
    List.length_singleton, List.length_reverse, count]
  omega

lemma restoreProgram_quantumTime (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    (restoreProgram stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 2 := by
  have count : (Enable.gates stream width bounded).length =
      2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 1 :=
    Enable.toggleGates_length (Enable.layout stream width bounded)
  have duration :
      (restoreProgram stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration =
        (restoreGates stream width bounded).length :=
    programList_quantumTime (encoding := Window.encoding)
      (QubitLayout.canonical Window.encoding.width) OracleModel.empty
      (restoreGates stream width bounded)
  rw [duration, restoreGates, List.length_append,
    List.length_singleton, count]

lemma full_prepare_native_counts (stream : Fin 2) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (prepareProgram stream 15 (by omega)).eventCost = 104 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (prepareProgram stream 15 (by omega)).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (prepareProgram stream 15 (by omega)).eventCost = 33 :=
  prepareProgram_native_counts stream 15 (by omega) (by omega)

lemma tail_prepare_native_counts (stream : Fin 2) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (prepareProgram stream 3 (by omega)).eventCost = 10 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (prepareProgram stream 3 (by omega)).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (prepareProgram stream 3 (by omega)).eventCost = 9 :=
  prepareProgram_native_counts stream 3 (by omega) (by omega)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Control
