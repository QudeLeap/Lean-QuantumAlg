/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Semantics
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Readout
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Reference

/-!
# Actual policy encoder with the same complete original sentinel-XOR action

The physical instruction list changes only through proved native test
words. Every encoded state has the same complete action as the original
encoder, including arbitrary old prefixes and arbitrary physical banks.
-/

namespace QuantumAlg.EncodedBit.FirstOne.TestPolicy

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)

/-- The same paid sentinel load precedes every actual policy-compiled original balanced emitter. -/
def encoderGates (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth) :
    List (GateSpec encoding) :=
  frame.sentinelGates ++ policy.gatesAt (Frame.priorityTree count height)
    (Frame.priorityTree_distinct capacity) 0
    (by have bounded := Frame.priorityTree_height (count := count) (depth := height); omega)

/-- The actual policy encoder remains an ordinary native circuit on the same complete layout. -/
def encoderProgram (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (policy.encoderGates height capacity fits)

/-- Every encoded input has exactly the original complete action, before imposing cleanliness. -/
lemma policyEncoderGates_eq_original (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (state : Data) :
    GateSpec.stepList (policy.encoderGates height capacity fits) state =
      GateSpec.stepList (frame.encoderGates height capacity fits) state := by
  simp only [encoderGates, Frame.encoderGates, GateSpec.stepList_append,
    policy.policy_gatesAt_step, frame.gatesAt_step]

/-- Every clean future-prefix input has the same original-root selected full-state XOR action. -/
lemma policyEncoderGates_step (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (state : Data) (clean : frame.CleanFrom 0 state) :
    GateSpec.stepList (policy.encoderGates height capacity fits) state =
      frame.positionXorStep state := by
  rw [policy.policyEncoderGates_eq_original]
  exact frame.encoderGates_step height capacity fits state clean

/-- Actual native policy semantics transfer to the original complete state action on every input. -/
lemma policyEncoderProgram_realizes (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (policy.encoderProgram height capacity fits) environment
      (GateSpec.stepList (frame.encoderGates height capacity fits)) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (policy.policyEncoderGates_eq_original height capacity fits) environment

/-- The complete physical native policy word maps every admitted encoded basis state exactly. -/
lemma policyEncoderProgram_apply_encoded_ket (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) (environment : OracleModel.empty.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    (policy.encoderProgram height capacity fits).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
          (encoding.encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical encoding.width).basisEquiv.symm
        (encoding.encode (frame.positionXorStep state))) := by
  have actual := (GateSpec.realizesList (QubitLayout.canonical _) .empty
    (policy.encoderGates height capacity fits) environment).apply_encoded_ket state
  rw [policy.policyEncoderGates_step height capacity fits state clean] at actual
  exact actual

end

end QuantumAlg.EncodedBit.FirstOne.TestPolicy
