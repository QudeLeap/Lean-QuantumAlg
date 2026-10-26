/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Program
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Actual native ledger of a moving-flag selector stream

Every retained callback executes its native coherent control lift and one
boundary CNOT. The ledger charges all static visits, including inactive
quantum branches, together with the reversible selector forks.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector.PayloadFamily

noncomputable section

open WindowLookup GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {frame : SelectorFrame encoding width}

private lemma callback_toffoli (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (label : Fin (2 ^ width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (family.callback physical oracles label).eventCost =
      ((family.payload label).source.map cnotMultiplicity).sum +
        4 * ((family.payload label).source.map toffoliMultiplicity).sum := by
  rw [callback, programList_toffoli_count_eq_sum]
  exact ((family.payload label).callback_counts _ _).2.2

private lemma callback_cnot (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (label : Fin (2 ^ width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (family.callback physical oracles label).eventCost =
      ((family.payload label).source.map xMultiplicity).sum + 1 := by
  rw [callback, programList_cnot_count_eq_sum]
  exact ((family.payload label).callback_counts _ _).2.1

private lemma callback_single (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (label : Fin (2 ^ width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (family.callback physical oracles label).eventCost = 0 := by
  rw [callback, programList_x_count_eq_sum]
  exact ((family.payload label).callback_counts _ _).1

private lemma callback_quantumTime (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (label : Fin (2 ^ width)) :
    (family.callback physical oracles label).evaluatedEventDepth Resource.Event.quantumDuration =
      ((family.payload label).source.map dirtyControlCount).sum + 1 := by
  rw [callback, programList_quantumTime, ControlledPayload.callbackGates, List.length_append]
  rw [ControlledPayload.gates, listWithDirtyControl_length]
  rfl

/-- Actual source CNOTs cost one Toffoli; source Toffolis cost four, plus reversible forks. -/
lemma program_toffoli_count (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (tree : SelectorTrie width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (family.program physical oracles tree).eventCost =
      2 * tree.forks + tree.leafSum (fun label =>
        ((family.payload label).source.map cnotMultiplicity).sum +
          4 * ((family.payload label).source.map toffoliMultiplicity).sum) := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount oracles (.gate .toffoli) = 2 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback_toffoli, Nat.mul_comm]

/-- Every boundary toggle and original source X is an actual additional CNOT. -/
lemma program_cnot_count (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (tree : SelectorTrie width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (family.program physical oracles tree).eventCost =
      tree.forks + tree.leafSum (fun label =>
        ((family.payload label).source.map xMultiplicity).sum + 1) := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount oracles (.gate .cnot) = 1 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback_cnot, Nat.mul_one]

/-- Single-qubit X gates belong exactly to the original five-gate reversible forks. -/
lemma program_single_count (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (tree : SelectorTrie width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (family.program physical oracles tree).eventCost =
      2 * tree.forks + tree.leafSum (fun _ => 0) := by
  rw [program, SelectorFrame.program_event_count]
  have forks : selectorForkCount oracles (.gate .singleQubit) = 2 := by
    simp [selectorForkCount]
  rw [forks]
  simp only [callback_single, Nat.mul_comm]

/-- Shared controls retain the actual sequential dependencies in each emitted native callback. -/
lemma program_quantumTime (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (tree : SelectorTrie width) :
    (family.program physical oracles tree).evaluatedEventDepth Resource.Event.quantumDuration =
      5 * tree.forks + tree.leafSum (fun label =>
        ((family.payload label).source.map dirtyControlCount).sum + 1) := by
  rw [program, SelectorFrame.program_quantumTime]
  simp only [callback_quantumTime]

end

end QuantumAlg.EncodedBit.StreamedSelector.PayloadFamily
