/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Redraw.Observation

/-!
# Joint law of a complete later EH batch

The real redraw picks one shared new source and derived parameter. All sixteen
later observations then pay for reset of the same physical bank. The theorem
keeps every external-reference block of the incoming state explicit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A later physical batch combines its own actual redraw with sixteen paid
same-bank members and copies into the preallocated terminal cells. -/
theorem nextBatch_joint_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : (ParameterShape N).Value → (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextBatch base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ value : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          (weight (parameterValue input value)
            (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) *
            ∏ index : Fin 16,
              Declared.sourceWeight N input (parameterValue input value) (outcomes index)))
      leftRef rightRef := by
  let redrawCircuit := redraw base noQuantum N input
  let resetRange := Circuit.forRange 16 (reusedSample base noQuantum N input)
  let observed : CInputRef (context base noQuantum N) (.bits (measurementBits N)) :=
    .storage (terminalRef base noQuantum N 0).toCStorageRef
  have separated := terminal_redraw_separated base noQuantum N 0
  have split := Circuit.referenceFiberSum_execute_seq redrawCircuit resetRange state
    (fun store => weight
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
      terminalIndicator base noQuantum N 16 id outcomes store)
    leftRef rightRef
  have conditional := reusedTerminals_reference base noQuantum N input
    (redrawCircuit.execute Reference state) weight outcomes leftRef rightRef
  have drawn := redraw_frame_reference base noQuantum N input observed separated state
    (fun _ parameter source => weight parameter source *
      ∏ index : Fin 16, Declared.sourceWeight N input parameter (outcomes index))
    leftRef rightRef
  exact split.trans (conditional.trans drawn)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
