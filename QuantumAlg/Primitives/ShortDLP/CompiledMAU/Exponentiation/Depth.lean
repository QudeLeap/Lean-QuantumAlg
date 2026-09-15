/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation.Resources
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Duration envelopes for the actual short-DLP exponentiation

A serial traversal of the independent native coordinate budget bounds every
nonnegative duration assignment. This envelope sums the separate coordinate
caps. The actual unit-duration depth equals the actual event count and obeys
the separately proved, tighter selected-multiplier bound.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

private def serialEvents (events : List (Resource.Event .quantum)) :
    DepthExpr (Resource.Event .quantum) :=
  events.foldr (fun event rest => .seq (.atom event) rest) .id

private theorem serialEvents_eval (assignment : Resource.Event .quantum → Nat)
    (events : List (Resource.Event .quantum)) :
    DepthExpr.depthEval assignment (serialEvents events) = (events.map assignment).sum := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      change assignment event + DepthExpr.depthEval assignment (serialEvents rest) =
        assignment event + (rest.map assignment).sum
      rw [ih]

/-- A serialized independent native pool, retaining all controlled event labels. -/
def exponentiationDepthEnvelope (bits width N : Nat) :
    DepthExpr (Resource.Event .quantum) :=
  serialEvents (exponentiationEventEnvelope bits width N).toList

/-- The envelope evaluates the independent pool at exactly the requested event durations. -/
theorem exponentiationDepthEnvelope_eval (bits width N : Nat)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment (exponentiationDepthEnvelope bits width N) =
      ResourcePool.weightedCount assignment (exponentiationEventEnvelope bits width N) := by
  rw [exponentiationDepthEnvelope, serialEvents_eval]
  calc
    _ = ResourcePool.weightedCount assignment
        (ResourcePool.ofList (exponentiationEventEnvelope bits width N).toList) :=
      (ResourcePool.weightedCount_ofList assignment _).symm
    _ = _ := congrArg (ResourcePool.weightedCount assignment)
      (Multiset.coe_toList (exponentiationEventEnvelope bits width N))

/-- Every actual member obeys the independent envelope under every duration assignment. -/
theorem exponentiationProgram_eventDepth_le (bits width N : Nat) (unit : (ZMod N)ˣ)
    (assignment : Resource.Event .quantum → Nat) :
    DepthExpr.depthEval assignment (exponentiationProgram bits width N unit).eventDepth ≤
      DepthExpr.depthEval assignment (exponentiationDepthEnvelope bits width N) := by
  rw [exponentiationDepthEnvelope_eval]
  apply DepthExpr.depthEval_le_weightedCount_of_eventPool_le
  change (exponentiationProgram bits width N unit).resourcesFromEventDepth ≤ _
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost]
  exact exponentiationProgram_eventCost_le bits width N unit

/-- Unit duration sums the independent coordinate caps, rather than the actual occurrences. -/
@[simp] theorem exponentiationDepthEnvelope_unit (bits width N : Nat) :
    DepthExpr.depthEval (fun _ => 1) (exponentiationDepthEnvelope bits width N) =
      exponentiationPrimitiveBound bits width N := by
  rw [exponentiationDepthEnvelope_eval, ← exponentiationEventEnvelope_card]
  simp [ResourcePool.weightedCount]

/-- The real selector serializes all native events, also at zero exponent or word width. -/
theorem exponentiationProgram_depth_eq_events (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).evaluatedEventDepth (fun _ => 1) =
      (exponentiationProgram bits width N unit).eventCost.card := by
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · rw [exponentiationProgram_valid bits width N positive fitted unit]
      exact MAU.Exponentiation.Gidney.gidneyExponent_depth_eq_events bits width
        ⟨N, Nat.lt_succ_of_le fitted⟩ unit
    · rw [exponentiationProgram_unfitted bits width N positive fitted unit]
      rfl
  · rw [exponentiationProgram_nonpositive bits width N positive unit]
    rfl

/-- The actual unit-duration serial depth satisfies the tighter total-occurrence bound. -/
theorem exponentiationProgram_actual_depth_bound (bits width N : Nat) (unit : (ZMod N)ˣ) :
    (exponentiationProgram bits width N unit).evaluatedEventDepth (fun _ => 1) ≤
      bits * MAU.Multiplication.Gidney.eventBound width := by
  rw [exponentiationProgram_depth_eq_events]
  exact exponentiationProgram_actual_event_bound bits width N unit

end

end QuantumAlg.ShortDLP.CompiledMAU
