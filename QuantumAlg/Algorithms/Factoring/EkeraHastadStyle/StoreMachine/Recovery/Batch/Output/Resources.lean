/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Independent chronological native formula for both literal output operations. -/
def events (N : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize
      (QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N))
      (modulusBits N)),
    .classicalOperation (.nominalEncoding (.packOption (modulusBits N)))]

/-- Independent context-free native multiplicity allowance. -/
def eventEnvelope (N : Nat) : ResourcePool kind := ResourcePool.ofList (events N)

/-- Every actual path executes exactly the native resize and native optional encoding. -/
theorem into_events (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).eventTrace path = events N := rfl

/-- Actual native multiplicities equal the independent two-instruction formula. -/
theorem into_resourcePool (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).resourcePool path = eventEnvelope N := rfl

/-- Every actual native coordinate meets the independent output allowance. -/
theorem into_pool_le (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope N := (into_resourcePool refs path).le

/-- Output production pays for both actual native operations. -/
theorem into_eventCount (refs : Refs ctx N) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 2 := rfl

/-- The payload resize precedes optional result packing in the dependency depth. -/
theorem into_depth (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 2 := rfl

/-- Every path meets the independent two-operation sequential depth allowance. -/
theorem into_depth_le (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤ 2 := (into_depth refs path).le

/-- Both actual writes retain the caller's entire live context. -/
theorem into_visited (refs : Refs ctx N) (path : (into refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ [ctx] at present
  simpa using present

/-- All caller cells and quantum dimensions remain resident through output packing. -/
theorem into_resident_le (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Every existing workspace role is included throughout actual output packing. -/
theorem into_auxiliary_le (refs : Refs ctx N) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Both native writes jointly restore borrowed storage with arbitrary external references. -/
theorem into_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ _
  · exact Circuit.borrowedRestored_classical _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput
