/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout.Resources

/-!
# Actual reused ECDLP sampling-round resources

Every round first measures, corrects and seeds all existing quantum systems,
then executes original exponent preparation, four conversions, all original
point calls, inverse QFT and terminal Z measurements. Exact duration keeps
the selected reset and scalar paths. No new input or clean-state condition
is required by these actual-code resource theorems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The complete reset branch allowance precedes all original sampling and readout events. -/
def samplingRoundBudget : ResourcePool .quantum :=
  samplingResetBudget E fieldTail (orderWidth problem) sameWidth fits seed +
    ((exponentPreparationCircuit problem).eventCost +
      (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale (2 * orderWidth problem) (MeasuredPointAddition.events p.size)) +
      (exponentReadoutCircuit problem).eventCost +
      (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2))

/-- Unit depth uses the true three-operation reset, independently of the branch pool cardinality. -/
def samplingRoundUnitDepth : Nat :=
  3 * (PublicInput.terminal E (orderWidth problem)).systemCount +
    ((exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
      (4 * MAU.Multiplication.Gidney.eventBound p.size +
        (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size) +
      (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
      2 * orderWidth problem)

/-- Every native reset, original exponent/arithmetic gate and terminal readout is included. -/
theorem samplingRound_pool_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).resourcePool path ≤
      samplingRoundBudget E fieldTail sameWidth fits problem seed := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (samplingReset_pool_le E fieldTail (orderWidth problem) sameWidth fits seed path.1)
    (samplingReadout_budget E fieldTail odd problem points path.2)

/-- The same selected reset history and scalar execution path determine arbitrary duration. -/
theorem samplingRound_duration (duration : Resource.Event .quantum → Nat)
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).depth duration path =
      (((samplingReset E fieldTail (orderWidth problem) sameWidth fits seed).eventTrace
        path.1).map duration).sum +
        ((exponentPreparationCircuit problem).evaluatedEventDepth duration +
          (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
            (Semantics.radixUnit p fieldTail.succ odd)).depth duration
              (samplingReadoutOriginalPath E fieldTail odd problem points path.2).1.2 +
          (exponentReadoutCircuit problem).evaluatedEventDepth duration +
          (2 * orderWidth problem) * duration (Circuit.zEvent 2)) :=
  congrArg₂ Nat.add
    (samplingReset_duration E fieldTail (orderWidth problem) sameWidth fits seed duration path.1)
    (samplingReadout_duration E fieldTail odd problem points duration path.2)

/-- The original unit-depth allowance follows actual reset and sampling sequentially. -/
theorem samplingRound_unitDepth_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).depth (fun _ => 1) path ≤
      samplingRoundUnitDepth E problem :=
  Nat.add_le_add
    (samplingReset_unitDepth E fieldTail (orderWidth problem) sameWidth fits seed path.1).le
    (samplingReadout_depth E fieldTail odd problem points path.2)

/-- Both stages reuse exactly the complete original terminal resident context. -/
theorem samplingRound_resident
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).peakResidentSpace path =
      (PublicInput.terminal E (orderWidth problem)).residentSpace :=
  (Circuit.peakResidentSpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (samplingReset_resident E fieldTail (orderWidth problem) sameWidth fits seed path.1)
      (samplingReadout_resident E fieldTail odd problem points path.2)).trans
        (SpacePool.max_self _))

/-- Every original auxiliary role and result cell remains counted in the reused context. -/
theorem samplingRound_auxiliary
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).peakAuxiliarySpace path =
      (PublicInput.terminal E (orderWidth problem)).auxiliarySpace :=
  (Circuit.peakAuxiliarySpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (samplingReset_auxiliary E fieldTail (orderWidth problem) sameWidth fits seed path.1)
      (samplingReadout_auxiliary E fieldTail odd problem points path.2)).trans
        (SpacePool.max_self _))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
