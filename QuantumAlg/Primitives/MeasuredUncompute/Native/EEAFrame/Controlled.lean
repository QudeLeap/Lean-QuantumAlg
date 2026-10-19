/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.Native.ReusedEEA

/-!
# Native coherent control of the complete forward and reused EEA frame

The original final control selects actual native lists. Every history and saved
word may start dirty; the exact coherent action and inverse restoration concern
the complete frame, including relative phases across control sectors.
-/

namespace QuantumAlg.MeasuredUncompute.NativeEEAFrame.Controlled

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ProductPlacement EncodedBit GateSpec MAU.Inversion.SharedEEA

/-- Actual forward instructions with the supplied final quantum control. -/
def forwardGates (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool) :
    List (GateSpec (NativeFrameControl.encoding modulus.size)) :=
  NativeFrameControl.gates modulus.size active (NativeEEAFrame.forwardGates modulus prime)

/-- Exact all-label conditional action of the complete forward list. -/
lemma nativeEEAControlled_forwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (state : Frame modulus.size × Bool) :
    stepList (forwardGates modulus prime active) state =
      NativeFrameControl.step modulus.size active
        (fun state => (InPlaceForward.step modulus state.1, state.2)) state := by
  rw [forwardGates, NativeFrameControl.nativeFrameControl_gates_step]
  unfold NativeFrameControl.step
  rw [nativeEEAFrame_forwardGates_step]

/-- Execute the literal forward list on the caller's unchanged complete layout. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  programList layout .empty (forwardGates modulus prime active)

/-- Exact phase-sensitive coherent forward semantics for all original labels. -/
lemma nativeEEAControlled_forward_realizes (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit.Realizes (layout := layout) (NativeFrameControl.encoding modulus.size)
      (forward modulus prime active layout) environment
      (NativeFrameControl.step modulus.size active
        (fun state => (InPlaceForward.step modulus state.1, state.2))) :=
  realizesList_congrStep layout .empty _
    (nativeEEAControlled_forwardGates_step modulus prime active) environment

/-- The forward trace is the actual expanded sequence in execution order. -/
lemma nativeEEAControlled_forward_trace (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (forward modulus prime active layout).eventTrace =
      (forwardGates modulus prime active).map (event .empty) :=
  programList_eventTrace layout .empty _

/-- Actual backward instructions with the supplied final quantum control. -/
def backwardGates (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool) :
    List (GateSpec (NativeFrameControl.encoding modulus.size)) :=
  NativeFrameControl.gates modulus.size active (NativeEEAFrame.backwardGates modulus prime)

/-- Exact all-label conditional action of the complete backward list. -/
lemma nativeEEAControlled_backwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (state : Frame modulus.size × Bool) :
    stepList (backwardGates modulus prime active) state =
      NativeFrameControl.step modulus.size active
        (NativeEEAFrame.backwardStep modulus prime) state := by
  rw [backwardGates, NativeFrameControl.nativeFrameControl_gates_step]
  unfold NativeFrameControl.step
  rw [nativeEEAFrame_backwardGates_step]

/-- Execute the literal backward list on the caller's unchanged complete layout. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  programList layout .empty (backwardGates modulus prime active)

/-- Exact phase-sensitive coherent backward semantics for all original labels. -/
lemma nativeEEAControlled_backward_realizes (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit.Realizes (layout := layout) (NativeFrameControl.encoding modulus.size)
      (backward modulus prime active layout) environment
      (NativeFrameControl.step modulus.size active (NativeEEAFrame.backwardStep modulus prime)) :=
  realizesList_congrStep layout .empty _
    (nativeEEAControlled_backwardGates_step modulus prime active) environment

/-- The backward trace is the actual expanded sequence in execution order. -/
lemma nativeEEAControlled_backward_trace (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (backward modulus prime active layout).eventTrace =
      (backwardGates modulus prime active).map (event .empty) :=
  programList_eventTrace layout .empty _

/-- Actual reusedForward instructions with the supplied final quantum control. -/
def reusedForwardGates (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool) :
    List (GateSpec (NativeFrameControl.encoding modulus.size)) :=
  (backwardGates modulus prime active).reverse

/-- Exact all-label conditional action of the complete reusedForward list. -/
lemma nativeEEAControlled_reusedForwardGates_step (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (state : Frame modulus.size × Bool) :
    stepList (reusedForwardGates modulus prime active) state =
      NativeFrameControl.step modulus.size active (NativeReusedEEA.step modulus) state := by
  rw [reusedForwardGates, backwardGates,
    NativeFrameControl.nativeFrameControl_reverseGates_step]
  unfold NativeFrameControl.step
  change (if state.2 = active then
    stepList (NativeReusedEEA.forwardGates modulus prime) state.1 else state.1, state.2) = _
  rw [NativeReusedEEA.nativeReusedEEA_forwardGates_step]

/-- Execute the literal reusedForward list on the caller's unchanged complete layout. -/
def reusedForward (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  programList layout .empty (reusedForwardGates modulus prime active)

/-- Exact phase-sensitive coherent reusedForward semantics for all original labels. -/
lemma nativeEEAControlled_reusedForward_realizes (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit.Realizes (layout := layout) (NativeFrameControl.encoding modulus.size)
      (reusedForward modulus prime active layout) environment
      (NativeFrameControl.step modulus.size active (NativeReusedEEA.step modulus)) :=
  realizesList_congrStep layout .empty _
    (nativeEEAControlled_reusedForwardGates_step modulus prime active) environment

/-- The reusedForward trace is the actual expanded sequence in execution order. -/
lemma nativeEEAControlled_reusedForward_trace (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (reusedForward modulus prime active layout).eventTrace =
      (reusedForwardGates modulus prime active).map (event .empty) :=
  programList_eventTrace layout .empty _

/-- Workspace reuse is the same FullPlacement before coherent control is expanded. -/
lemma nativeEEAControlled_backward_placed (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) :
    backwardGates modulus prime active = NativeFrameControl.gates modulus.size active
      ((NativeEEAFrame.forwardGates modulus prime).reverse.map
        (WorkspaceReuse.placement modulus.size).placeGate) := rfl

/-- Reused forward is the literal ordered reverse of the expanded backward word. -/
lemma nativeEEAControlled_reusedForward_reversed (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) :
    reusedForwardGates modulus prime active = (backwardGates modulus prime active).reverse := rfl

/-- The actual inverse trace reverses every expanded native instruction, including wrappers. -/
lemma nativeEEAControlled_reusedForward_reverse_trace (modulus : Nat)
    (prime : Nat.Prime modulus) (active : Bool)
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (reusedForward modulus prime active layout).eventTrace =
      (backward modulus prime active layout).eventTrace.reverse := by
  rw [nativeEEAControlled_reusedForward_trace, nativeEEAControlled_backward_trace,
    reusedForwardGates, List.map_reverse]

/-- Both selected and unselected sectors restore arbitrary dirty frames after inverse execution. -/
lemma nativeEEAControlled_reusedForward_backward_restores (modulus : Nat)
    (prime : Nat.Prime modulus) (active : Bool) (state : Frame modulus.size × Bool) :
    stepList (reusedForwardGates modulus prime active)
      (stepList (backwardGates modulus prime active) state) = state := by
  rw [reusedForwardGates]
  exact stepList_reverse_stepList _ _

-- Saved-word projections use the established frame interface, not recursive gate evaluation.
attribute [local irreducible] NativeEEAFrame.backwardGates NativeReusedEEA.forwardGates
  WorkspaceReuse.placement

/-- The arbitrary saved target survives the controlled placed adjoint in both sectors. -/
lemma nativeEEAControlled_backward_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (state : Frame modulus.size × Bool) :
    ((WorkspaceReuse.placement modulus.size).grouping
      (stepList (backwardGates modulus prime active) state).1).2 =
      ((WorkspaceReuse.placement modulus.size).grouping state.1).2 := by
  rw [backwardGates, NativeFrameControl.nativeFrameControl_gates_step]
  unfold NativeFrameControl.step
  split
  · exact nativeEEAFrame_backward_saved modulus prime state.1
  · rfl

/-- The arbitrary saved target survives controlled reused forward in both sectors. -/
lemma nativeEEAControlled_reusedForward_saved (modulus : Nat) (prime : Nat.Prime modulus)
    (active : Bool) (state : Frame modulus.size × Bool) :
    ((WorkspaceReuse.placement modulus.size).grouping
      (stepList (reusedForwardGates modulus prime active) state).1).2 =
      ((WorkspaceReuse.placement modulus.size).grouping state.1).2 := by
  rw [reusedForwardGates, backwardGates,
    NativeFrameControl.nativeFrameControl_reverseGates_step]
  unfold NativeFrameControl.step
  split
  · simpa only [NativeReusedEEA.forwardGates] using
      NativeReusedEEA.nativeReusedEEA_forward_saved modulus prime state.1
  · rfl

end

end QuantumAlg.MeasuredUncompute.NativeEEAFrame.Controlled
