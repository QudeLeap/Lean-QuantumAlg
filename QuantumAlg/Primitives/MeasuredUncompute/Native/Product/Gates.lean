/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Gates
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal product instructions on the complete measured frame

Every gate is lifted past the existing history and moved by the same complete
wire placement as the native product. The full action and ordered trace remain
those of that original program; no preparation or extra physical wire occurs.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame

noncomputable section

open MAU.Multiplication ProductPlacement EncodedBit GateSpec

/-- The original three-word instructions with the complete history retained. -/
private def sourceGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (BinaryLabelEncoding.prod (VariableGidney.encoding width)
      (BinaryLabelEncoding.finIdentity (historyWidth width)))) :=
  (VariableGidney.gates width modulus).map
    (GateSpec.prodLeft (BinaryLabelEncoding.finIdentity (historyWidth width)))

/-- The same actual native instructions at the original measured arithmetic ports. -/
def gates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (frameEncoding width)) :=
  (sourceGates width modulus).map (placement width).placeGate

/-- Exact whole-frame action, including all retained history positions. -/
lemma nativeProductFrame_gates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width) : stepList (gates width modulus) state = step width modulus state := by
  have lifted := stepList_prodLeft (left := VariableGidney.encoding width)
    (BinaryLabelEncoding.finIdentity (historyWidth width))
    (VariableGidney.gates width modulus) ((placement width).grouping state)
  have original := VariableGidney.variableGidney_gates_step width modulus
    ((placement width).grouping state).1
  exact ((placement width).placeGates_step (sourceGates width modulus) state).trans
    ((congrArg (placement width).grouping.symm lifted).trans
      (congrArg (fun result =>
        (placement width).grouping.symm (result, ((placement width).grouping state).2))
        original))

/-- Literal lifting and full placement keep the original ordered native trace. -/
lemma nativeProductFrame_gates_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).map (event .empty) = (program width modulus).eventTrace := by
  have placed : (gates width modulus).map (event .empty) =
      (sourceGates width modulus).map (event .empty) := by
    exact (programList_eventTrace (QubitLayout.canonical _) .empty
      (gates width modulus)).symm.trans
        ((placement width).placeGates_eventTrace (QubitLayout.canonical _) .empty
          (sourceGates width modulus))
  have lifted := map_event_prodLeft (oracles := .empty)
    (left := VariableGidney.encoding width)
    (BinaryLabelEncoding.finIdentity (historyWidth width))
    (VariableGidney.gates width modulus)
  exact placed.trans (lifted.trans
    ((VariableGidney.variableGidney_gates_trace width modulus).trans
      (nativeProductFrame_trace width modulus).symm))

/-- The original independent product bound is unchanged by the physical gate placement. -/
lemma nativeProductFrame_gates_length_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).length ≤ VariableGidney.eventBound width := by
  have placed : (gates width modulus).length = (sourceGates width modulus).length :=
    List.length_map (f := (placement width).placeGate) (as := sourceGates width modulus)
  have lifted := length_prodLeft (left := VariableGidney.encoding width)
    (BinaryLabelEncoding.finIdentity (historyWidth width))
    (VariableGidney.gates width modulus)
  exact (placed.trans lifted).le.trans
    (VariableGidney.variableGidney_gates_length_bound width modulus)

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame
