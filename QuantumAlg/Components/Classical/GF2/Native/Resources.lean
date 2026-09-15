/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native
import all QuantumAlg.Components.Classical.GF2.Native.Echelon.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Validation.Resources

/-!
# Actual resources of complete same-context GF(2) recovery

The original prefix, complement, single NOT and decision are followed by the
three actual success branches and the final real packOption. Bounds retain
each component's original native allowance. Durations and counts are read
from the same complete actual path, without asserting reachable-path tightness.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original packOption event retains the candidate's actual machine width. -/
def gf2OutputPackEvent (kind : ProblemKind) (width : Nat) : Resource.Event kind :=
  .classicalOperation (.nominalEncoding (.packOption width))

/-- The actual final instruction emits exactly its original optional encoding event. -/
theorem gf2PackOutput_events (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (packOutput success candidate output).Path) :
    (packOutput success candidate output).eventTrace path = [gf2OutputPackEvent kind width] := rfl

/-- All original native stage allowances are added in their actual chronological order. -/
def intoEnvelope (kind : ProblemKind) (rowCount width : Nat) : ResourcePool kind :=
  ((ResourcePool.scale rowCount (rowEnvelope kind rowCount width) + echelonEnvelope kind
    rowCount width) + (ResourcePool.singleton (.classicalOperation (.wordUnary .complement
    width)) + (ResourcePool.singleton (.classicalOperation (.bit .not)) + (uniqueFreeEnvelope
    kind width + (candidateEnvelope kind rowCount width + (decisionTestEnvelope kind width +
    (validationEnvelope kind rowCount width + ResourcePool.singleton (gf2OutputPackEvent kind
    width))))))))

/-- Each original stage retains its arbitrary-duration allowance in the same sequence. -/
def intoDepthLimit (rowCount width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  ((rowCount * rowDepthLimit rowCount width duration + echelonDepthLimit rowCount width
    duration) + (duration (.classicalOperation (.wordUnary .complement width)) + (duration
    (.classicalOperation (.bit .not)) + (uniqueFreeDepthLimit width duration +
    (candidateDepthLimit rowCount width duration + (decisionTestDepthLimit width duration +
    (validationDepthLimit rowCount width duration + duration (gf2OutputPackEvent kind
    width))))))))

private theorem when_pool_le (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (budget : ResourcePool kind) (bound : ∀ path, body.resourcePool path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).resourcePool path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (0 : ResourcePool kind) ≤ _
        exact zero_le
      · exact bound path

private theorem when_depth_le (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (duration : Resource.Event kind → Nat) (budget : Nat)
    (bound : ∀ path, body.depth duration path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).depth duration path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact bound path

private theorem when_duration (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (duration : Resource.Event kind → Nat)
    (equation : ∀ path, body.depth duration path = ((body.eventTrace path).map duration).sum)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).depth duration path =
      (((whenSuccessful success body).eventTrace path).map
        duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact equation path

private theorem serial_pool_le (first second : Circuit ctx ctx)
    (leftBudget rightBudget : ResourcePool kind)
    (left : ∀ path, first.resourcePool path ≤ leftBudget)
    (right : ∀ path, second.resourcePool path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).resourcePool path ≤ leftBudget + rightBudget := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (left path.1) (right path.2)

private theorem serial_depth_le (first second : Circuit ctx ctx)
    (duration : Resource.Event kind → Nat) (leftBudget rightBudget : Nat)
    (left : ∀ path, first.depth duration path ≤ leftBudget)
    (right : ∀ path, second.depth duration path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).depth duration path ≤ leftBudget + rightBudget :=
  Nat.add_le_add (left path.1) (right path.2)

private theorem serial_duration (first second : Circuit ctx ctx)
    (duration : Resource.Event kind → Nat)
    (left : ∀ path, first.depth duration path = ((first.eventTrace path).map duration).sum)
    (right : ∀ path, second.depth duration path = ((second.eventTrace path).map duration).sum)
    (path : (first.seq second).Path) :
    (first.seq second).depth duration path =
      (((first.seq second).eventTrace path).map
        duration).sum := by
  change first.depth duration path.1 + second.depth duration path.2 =
    ((first.eventTrace path.1 ++ second.eventTrace path.2).map duration).sum
  rw [List.map_append, List.sum_append]
  exact congrArg₂ (· + ·) (left path.1) (right path.2)

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns candidate zero : CWriteRef ctx (.unsignedWord width))
  (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- The original complete circuit charges all native stages and its final actual packing. -/
theorem gf2Into_pool_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).resourcePool path ≤
      intoEnvelope kind rowCount width :=
  (serial_pool_le _ _ _ _ (gf2LoadAndReduce_pool_le matrix used rows columns input)
  (serial_pool_le _ _ _ _ ((fun _path => le_rfl))
  (serial_pool_le _ _ _ _ ((fun _path => le_rfl))
  (serial_pool_le _ _ _ _ (gf2UniqueFree_pool_le columns zero success)
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2BuildCandidate_pool_le matrix rows
    columns candidate zero))
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2CandidateNonzero_pool_le candidate zero
    success))
  (serial_pool_le _ _ _ _ (when_pool_le success _ _ (gf2ValidationSamples_pool_le input
    candidate success))
  ((fun _path => le_rfl))))))))) path

/-- The complete original dependency order retains every actual event-duration allowance. -/
theorem gf2Into_depth_le (duration : Resource.Event kind → Nat)
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).depth duration path ≤
      intoDepthLimit rowCount width duration :=
  (serial_depth_le _ _ duration _ _ (gf2LoadAndReduce_depth_le matrix used rows columns input
    duration)
  (serial_depth_le _ _ duration _ _ ((fun _path => le_rfl))
  (serial_depth_le _ _ duration _ _ ((fun _path => le_rfl))
  (serial_depth_le _ _ duration _ _ (gf2UniqueFree_depth_le columns zero success duration)
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2BuildCandidate_depth_le matrix rows columns candidate zero duration))
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2CandidateNonzero_depth_le candidate zero success duration))
  (serial_depth_le _ _ duration _ _ (when_depth_le success _ duration _
    (gf2ValidationSamples_depth_le input candidate success duration))
  ((fun _path => le_rfl))))))))) path

/-- Exact duration is the sum of the events emitted by that same complete actual path. -/
theorem gf2Into_duration_eventTrace (duration : Resource.Event kind → Nat)
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).depth duration path =
      (((into input matrix used rows columns candidate zero success output).eventTrace path).map
        duration).sum :=
  (serial_duration _ _ duration (gf2LoadAndReduce_duration_eventTrace matrix used rows columns
    input duration)
  (serial_duration _ _ duration ((fun _path => (Nat.add_zero _).symm))
  (serial_duration _ _ duration ((fun _path => (Nat.add_zero _).symm))
  (serial_duration _ _ duration (gf2UniqueFree_duration_eventTrace columns zero success
    duration)
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2BuildCandidate_duration_eventTrace matrix rows columns candidate zero duration))
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2CandidateNonzero_duration_eventTrace candidate zero success duration))
  (serial_duration _ _ duration (when_duration success _ duration
    (gf2ValidationSamples_duration_eventTrace input candidate success duration))
  ((fun _path => (Nat.add_zero _).symm))))))))) path

/-- The actual native instruction count is bounded by the original unit-duration stage sum. -/
theorem gf2Into_eventCount_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    ((into input matrix used rows columns candidate zero success output).eventTrace path).length ≤
      intoDepthLimit (kind := kind) rowCount width (fun _ => 1) := by
  have bound := gf2Into_depth_le input matrix used rows columns candidate zero success output
    (fun _ => 1) path
  rw [gf2Into_duration_eventTrace] at bound
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one] using bound

end

end QuantumAlg.ClassicalRoutines.GF2.Native
