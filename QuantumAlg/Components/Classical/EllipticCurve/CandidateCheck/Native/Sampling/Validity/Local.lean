/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Observation

/-!
# Arbitrary selected-value invariants through actual local sampling

The seven existing cells move only into the reference/history coordinates
of the same local execution. Observing the truth value of any predicate on
the actual acceptance bit and selected word therefore preserves that
predicate on all positive blocks. The words may differ between branches.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Actual local sampling preserves every supported property of the retained selection pair. -/
theorem underPersistent_latches_property
    (code : Circuit model ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    (property : Bool × (CShape.unsignedWord scalarWidth).Value → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      property ((entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
          entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (underPersistent code supported width scalarWidth).Path)))
    (positive : 0 < (((underPersistent code supported width scalarWidth).execute
      Reference state).block result).mass) :
    property ((result.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) := by
  classical
  have kept := retained_observation_supported (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth)
    (@persistentStores_mass model.kind ctx width scalarWidth)
    code (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth)
    (@persistentCoordinates_execute model ctx code supported width scalarWidth)
    (fun history => decide (property (savedLatches width scalarWidth history))) true state
    (fun original positive => by
      apply decide_eq_true
      exact (congrArg property (persistentStores_latches width scalarWidth original.1)).mpr
        (holds original positive)) result positive
  have valid := of_decide_eq_true kept
  exact (congrArg property (persistentStores_latches width scalarWidth result.1)).mp valid

/-- Local sampling preserves any supported predicate of the retained selected
word, without requiring an identical word across input branches. -/
theorem underPersistent_selected_property
    (code : Circuit model ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    (property : (CShape.unsignedWord scalarWidth).Value → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read
        (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (underPersistent code supported width scalarWidth).Path)))
    (positive : 0 < (((underPersistent code supported width scalarWidth).execute
      Reference state).block result).mass) :
    property (result.1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) := by
  exact underPersistent_latches_property code supported width scalarWidth
    (fun pair => property pair.2) state holds result positive

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
