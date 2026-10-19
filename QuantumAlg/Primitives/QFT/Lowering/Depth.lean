/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.Swap

/-! # Dependency depth of the actual Fourier gate expansion -/

namespace QuantumAlg.QuantumFourierTransform.Lowering
noncomputable section

/-- Unit-duration standard-model depths of the three executed local words. -/
public def standardDuration : Resource.Event (.quantum FourierGate.model .empty) → Nat
  | .gate .hadamard => 1
  | .gate .controlledPhase => 5
  | .gate .swap => 3
  | _ => 0

private lemma nativeRealization_depth (oracles : OracleModel) {count : Nat}
    {layout : QuantumLayout count} (application : GateModel.Application FourierGate.model layout) :
    (nativeRealization oracles application).circuit.evaluatedEventDepth (fun _ => 1) =
      standardDuration (.gate application.coordinate) := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  change (UnitaryCircuit.placeAt _ _ _ _
    (localRealization oracles token).circuit).evaluatedEventDepth (fun _ => 1) = _
  rw [UnitaryCircuit.placeAt_evaluatedEventDepth]
  cases token <;> rfl

/-- Refinement retains sums and parallel maxima and uses the true local expansion depths. -/
public lemma lower_unit_depth (oracles : OracleModel) {count : Nat}
    {layout : QuantumLayout count} (source : UnitaryCircuit FourierGate.model .empty layout) :
    (lower oracles source).evaluatedEventDepth (fun _ => 1) =
      source.evaluatedEventDepth standardDuration := by
  apply UnitaryCircuit.refine_evaluatedEventDepth source (instructions oracles)
    standardDuration (fun _ => 1)
  · exact nativeRealization_depth oracles
  · intro width ambient application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

end
end QuantumAlg.QuantumFourierTransform.Lowering
