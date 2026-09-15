/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Observation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness

/-!
# Original selected ECDLP readouts satisfy the actual candidate condition

The finite vector is read in precisely its original order. The original
selected-family recovery theorem supplies the recovered scalar and both
flags, and the original subgroup equation supplies its natural point check.
The secret occurs only in this proof, never in the executable interface.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual raw decoder sees exactly the original ordered terminal outcome. -/
theorem nativeECDLP_preparationInput (I : ECDLPInstance E)
    (sampleValue : CShape.Value (.fixedVector (sampleWidth I) (.finite 2))) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput sampleValue =
      .bits (observedOutcome I sampleValue) := rfl

/-- Each original selected outcome satisfies the complete actual candidate condition. -/
theorem nativeECDLP_selected_sampleAccepted (I : ECDLPInstance E)
    (sampleValue : CShape.Value (.fixedVector (sampleWidth I) (.finite 2)))
    (selected : observedOutcome I sampleValue ∈
      FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I)) :
    SampleAccepted (Layout.curveSpec E) (recoveryModulus I)
      I.basePoint.toMathlib I.targetPoint.toMathlib sampleValue := by
  let : Fact p.Prime := ⟨E.prime⟩
  obtain ⟨unit, _, same⟩ := Finset.mem_image.mp selected
  have rawInput : ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput
      sampleValue =
      FiniteCyclicDLP.Probability.RecoveryBridge.selectedRawInput (problem I) (input I) unit := by
    rw [nativeECDLP_preparationInput]
    exact congrArg CShape.Value.bits same.symm
  obtain ⟨result, recovered, candidate, verified⟩ :=
    FiniteCyclicDLP.Probability.RecoveryBridge.outputOf_selectedRawInput_recovers
      (problem I) (input I) unit (recoveryModulus I) rfl
  have values := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    (recoveryModulus I) _ result recovered
  have fits : (input I).secret.val < 2 ^ FiniteCyclicDLP.orderWidth (problem I) :=
    lt_of_lt_of_le (FiniteCyclicDLP.Probability.residueIndex (problem I) (input I).secret).isLt
      (FiniteCyclicDLP.order_le_fourierModulus (problem I))
  unfold SampleAccepted
  rw [rawInput, values, candidate, verified]
  change ((input I).secret.val % 2 ^ FiniteCyclicDLP.orderWidth (problem I)) •
    I.basePoint.toMathlib = I.targetPoint.toMathlib ∧ true = true ∧ true = true
  rw [Nat.mod_eq_of_lt fits]
  exact ⟨Measured.secret_groupScalar_eq_target (problem I) (input I), rfl, rfl⟩

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
