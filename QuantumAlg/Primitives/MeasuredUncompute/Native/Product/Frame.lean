/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Native variable multiplication on the existing measured-arithmetic ports

The existing three-word product is placed on X, Y, A inside the complete
shared-EEA frame. The same program determines its complete basis action,
event allowance, duration and original physical footprint. The small
arithmetic history remains present throughout this operation
[LYL+26, sec_point_add/sec_point_add.tex:51-105].
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame

noncomputable section

open MAU.Multiplication ProductPlacement

private def body (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (sourceEncoding width).width) :=
  UnitaryCircuit.prodLeft (n := historyWidth width) (VariableGidney.program width modulus)

private theorem body_within (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (body width modulus).physical_idx ⊆ List.range (sourceEncoding width).width := by
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  rw [VariableGidney.variableGidney_physical]
  have count : (VariableGidney.encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  rw [count]
  exact List.Subset.refl _

/-- Execute the actual native product on the three existing ports in the complete shared frame. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (frameEncoding width).width) :=
  (placement width).place (body width modulus) (body_within width modulus)

/-- Reassemble the independent arithmetic action and retained history through real ports. -/
def step (width : Nat) (modulus : Fin (2 ^ width + 1)) : Frame width → Frame width :=
  (placement width).step
    (fun state => (VariableGidney.prefixOutput modulus width state.1, state.2))

/-- Every complete basis label follows the actual placed product with its full retained frame. -/
theorem nativeProductFrame_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (frameEncoding width) (program width modulus) (step width modulus) :=
  (placement width).place_realizes (body_within width modulus)
    (UnitaryCircuit.Realizes.prodLeft
      (right := BinaryLabelEncoding.finIdentity (historyWidth width))
      (VariableGidney.variableGidney_realizes width modulus))

/-- Re-encoding changes no emitted event, and retaining the small frame performs no extra gate. -/
theorem nativeProductFrame_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventTrace = (VariableGidney.program width modulus).eventTrace := by
  rw [program, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.prodLeft_eventTrace _

/-- The same independent native product allowance bounds the actual placed operation. -/
theorem nativeProductFrame_budget (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost ≤ VariableGidney.nativeBudget width := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProductFrame_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact VariableGidney.variableGidney_native_budget width modulus

/-- The original complete frame remains live; no system is added or released by placement. -/
theorem nativeProductFrame_physical (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).physical_idx =
      List.range (3 * width + 11 + 4 * width.size) := by
  rw [program, EncodedBit.FullPlacement.place_physical, frame_width]
  have count : ProductWires.width width (tailWidth width) = 3 * width + 11 + 4 * width.size := by
    unfold ProductWires.width tailWidth
    omega
  rw [count]

/-- The serial depth comes from precisely the same native product events. -/
theorem nativeProductFrame_depth (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).evaluatedEventDepth (fun _ => 1) ≤
      VariableGidney.eventBound width := by
  rw [program, EncodedBit.FullPlacement.place_evaluatedEventDepth]
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (UnitaryCircuit.prodLeft (n := historyWidth width) (VariableGidney.program width modulus)) ≤ _
  rw [UnitaryCircuit.prodLeft_evaluatedEventDepth]
  exact VariableGidney.variableGidney_unit_depth width modulus

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame
