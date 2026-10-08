/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint

/-!
# Ordered traces of coordinate-preserving native adjoints

When each inverse implementation emits the original single coordinate, the
constructed adjoint reverses the complete expanded trace, including indexed
products, repetitions and disjoint parallel branches.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}

private theorem reverseWords_eventTrace {count : Nat} {layout : QuantumLayout count}
    (words : List (UnitaryCircuit gates oracles layout)) :
    (reverseWords words).eventTrace = (words.reverse.map eventTrace).flatten := by
  induction words with
  | nil => rfl
  | cons next rest ih =>
      change (reverseWords rest |>.seq next).eventTrace = _
      simp only [seq_eventTrace, ih, List.reverse_cons,
        List.map_append, List.map_singleton, List.flatten_append, List.flatten_singleton]

/-- Singleton inverse implementations reverse the actual complete ordered event word. -/
public theorem dagger_eventTrace_of_singletons
    (implementations : AdjointRealizations gates oracles gates oracles)
    (nativeTrace : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : GateModel.Application gates layout),
      (implementations.native application).circuit.eventTrace = [.gate application.coordinate])
    (queryTrace : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : OracleModel.Application oracles layout),
      (implementations.query application).circuit.eventTrace = [.oracle application.coordinate])
    {count : Nat} {layout : QuantumLayout count} (circuit : UnitaryCircuit gates oracles layout) :
    (circuit.dagger implementations).eventTrace = circuit.eventTrace.reverse := by
  obtain ⟨sequence⟩ := circuit
  change (inverseSequence implementations sequence).circuit.eventTrace =
    (UnitarySequence.eventTrace sequence).reverse
  induction sequence with
  | id => rfl
  | leaf atom =>
      cases atom with
      | gate application => exact nativeTrace application
      | oracle application => exact queryTrace application
  | seq left right leftIH rightIH =>
      simp only [inverseSequence, seq_eventTrace, UnitarySequence.eventTrace,
        List.reverse_append, rightIH, leftIH]
  | embed placement body bodyIH =>
      simpa only [inverseSequence, embed_eventTrace, UnitarySequence.eventTrace] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change (inverseSequence implementations right).circuit.eventTrace ++
        (inverseSequence implementations left).circuit.eventTrace = _
      rw [leftIH, rightIH]
      exact List.reverse_append.symm
  | iterate repetitions body bodyIH =>
      simp only [inverseSequence, iterate_eventTrace, bodyIH, UnitarySequence.eventTrace,
        List.reverse_flatten, List.map_replicate, List.reverse_replicate]
  | indexedProduct label steps start step startIH stepIH =>
      simp only [inverseSequence, seq_eventTrace, reverseWords_eventTrace, startIH,
        UnitarySequence.eventTrace, List.reverse_append, List.reverse_flatten,
        List.map_reverse, List.map_ofFn, Function.comp_def, stepIH]
  | macroCall name body bodyIH =>
      simpa only [inverseSequence, macroCall_eventTrace, UnitarySequence.eventTrace] using bodyIH

end

end QuantumAlg.UnitaryCircuit
