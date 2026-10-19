/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Mathematics
public import QuantumAlg.Core.Execution.QubitReadouts
public import QuantumAlg.Core.Execution.Context.Layout
public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Real message storage and physical Bell-pair interfaces

Each source block has two supplied qubits, two borrowed classical message
bits, and two distinct writable finite result cells. Output reads the actual
results in message order, reversing the decoder's physical order b,a
[dW19, qcnotes.tex:879-890]. No stored result is synthesized from the input.
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

/-- Recursive physical width, preserving the actual two-system append at each block. -/
public def width : Nat → Nat
  | 0 => 0
  | count + 1 => width count + 2

lemma width_eq (count : Nat) : width count = count * 2 := by
  induction count with
  | zero => rfl
  | succ count ih => rw [width, ih]; omega

/-- Original physical systems of all supplied Bell pairs. -/
public abbrev layout (count : Nat) :=
  (QuantumSignature.qubits (width count)).canonicalPlacement.layout

/-- A single pair in its source big-endian physical order. -/
public abbrev blockLayout := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The source message contains two finite binary values per block. -/
public abbrev messageShape (count : Nat) : CShape :=
  .fixedVector count (.product (.finite 2) (.finite 2))

/-- Both shared Bell halves are supplied mutable interface systems. -/
def quantumContext (count : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨0⟩ (layout count) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma input_fresh (count : Nat) :
    (⟨1⟩ : StorageKey) ∉ (quantumContext count).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The classical input is genuine borrowed storage, preserved by execution. -/
def inputContext (count : Nat) : RuntimeCtx .quantum :=
  (quantumContext count).addBorrowedInput ⟨1⟩ (messageShape count) (input_fresh count)

/-- The complete fixed context also contains one actual result cell per measured wire. -/
public def context (count : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (inputContext count) 2 (width count)

/-- The branch reads the original message cell through the retained-result context. -/
public def messageInput (count : Nat) : CInputRef (context count) (messageShape count) :=
  MeasurementCells.liftInput 2 (.storage (CStorageRef.borrowedInputHead (quantumContext count) ⟨1⟩
    (messageShape count) (input_fresh count))) (width count)

lemma context_wires (count : Nat) :
    (layout count).wires = (context count).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, context, MeasurementCells.context_quantumWires]
  change (layout count).wires = (layout count).wires ++ []
  exact (List.append_nil _).symm

def position (count : Nat) : Fin (width count) ≃ Fin (context count).systemCount :=
  positionsOfEqualWires _ _ (context_wires count)

lemma position_dimension (count : Nat) (index : Fin (width count)) :
    ((context count).quantumLayout.wire (position count index)).dimension = 2 := by
  rw [position, wireAtCorrespondingPosition]
  rfl

/-- The original block and side indices determine the actual physical wire. -/
def wireIndex {count : Nat} (block : Fin count) (side : Fin 2) : Fin (width count) :=
  Fin.cast (width_eq count).symm (finProdFinEquiv (block, side))

/-- Each measurement has a separate actual binary destination. -/
public def resultCell (count : Nat) (index : Fin (width count)) :
    CWriteRef (context count) (.finite 2) :=
  MeasurementCells.reference (inputContext count) 2 (width count) index

/-- Bob reads a from the second physical wire and b from the first, without computing new bits. -/
public def resultInput (count : Nat) : CInputRef (context count) (messageShape count) :=
  .fixedVector fun block => .product
    (.storage (resultCell count (wireIndex block 1)).toCStorageRef)
    (.storage (resultCell count (wireIndex block 0)).toCStorageRef)

/-- Every supplied physical qubit is actually measured into its own result cell. -/
public def readouts (count : Nat) : List (ZReadout (context count)) :=
  QubitReadouts.readouts (position count) (position_dimension count) (resultCell count)

end
end QuantumAlg.SuperdenseCoding.Execution
