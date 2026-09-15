/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Original sampling gates on the complete allocated arithmetic context

The original exponent preparation, converted measured scalar cascade and
inverse QFT act on the same already live systems. This local circuit is the
quantum prefix used between the real preparation/reset and terminal readout
stages of workspace reuse. Its syntax adds no allocation and requires no
state or initialization witness. Correct preparation and its probability
connection are separate obligations of the surrounding actual execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Run the original exponent gates and measured arithmetic on the existing complete workspace. -/
def samplingPrefix (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    Circuit (Allocation.after p.size (2 * orderWidth problem))
      (Allocation.after p.size (2 * orderWidth problem)) :=
  ((afterExponentCircuit p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem)).seq
    (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd))).seq (afterExponentReadout p problem)

/-- Every actual instruction acts within the same existing local quantum and classical context. -/
theorem samplingPrefix_isLocal (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    (samplingPrefix E fieldTail odd problem points).IsLocal :=
  ⟨⟨trivial, Encoding.placedConvertedCascade_isLocal E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)⟩,
      trivial⟩

/-- Native gates include both original exponent programs, four conversions and all point calls. -/
theorem samplingPrefix_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (samplingPrefix E fieldTail odd problem points).Path) :
    (samplingPrefix E fieldTail odd problem points).resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
          ResourcePool.scale (2 * orderWidth problem) (MeasuredPointAddition.events p.size)) +
        (exponentReadoutCircuit problem).eventCost := by
  change ResourcePool.ofList ((_ ++ _) ++ _) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  have scalar := Encoding.placedConvertedCascade_budget E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd) path.1.2
  rw [List.length_finRange] at scalar
  exact add_le_add (add_le_add
    (afterExponentCircuit_cost p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem) path.1.1).le scalar)
    (afterExponentCircuit_cost p (orderWidth problem) (exponentReadoutCircuit problem)
      (exponentReadoutCircuit_physical_idx problem) path.2).le

/-- The original serial durations are charged on the same existing-workspace path. -/
theorem samplingPrefix_duration (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (duration : Resource.Event .quantum → Nat)
    (path : (samplingPrefix E fieldTail odd problem points).Path) :
    (samplingPrefix E fieldTail odd problem points).depth duration path =
      (exponentPreparationCircuit problem).evaluatedEventDepth duration +
        (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
          (Semantics.radixUnit p fieldTail.succ odd)).depth duration path.1.2 +
        (exponentReadoutCircuit problem).evaluatedEventDepth duration := by
  change (_ + _) + _ = _
  exact congrArg₂ Nat.add (congrArg₂ Nat.add
    (afterExponentCircuit_depth p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem) duration path.1.1) rfl)
    (afterExponentCircuit_depth p (orderWidth problem) (exponentReadoutCircuit problem)
      (exponentReadoutCircuit_physical_idx problem) duration path.2)

/-- The actual local prefix visits only its original complete allocated context. -/
theorem samplingPrefix_visited (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (samplingPrefix E fieldTail odd problem points).Path)
    (visited : RuntimeCtx .quantum)
    (present : visited ∈ (samplingPrefix E fieldTail odd problem points).visitedContexts path) :
    visited = Allocation.after p.size (2 * orderWidth problem) :=
  local_visited _ (samplingPrefix_isLocal E fieldTail odd problem points) path visited present

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
