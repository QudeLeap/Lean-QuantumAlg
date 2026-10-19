/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Geometry
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Complete physical interface of parallel teleportation

Each source block retains Alice's unknown input, Alice's Bell half, Bob's
Bell half, and the two actual measured results [dW19, qcnotes.tex:785-804].
The unknown inputs belong to one joint register and may be mutually
entangled and entangled with the external reference [dW19, qcnotes.tex:809].
Neither the layout nor the classical result cells impose a product state.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution

/-- Recursive physical width matches the existing consecutive parallel constructor. -/
public def width : Nat → Nat
  | 0 => 0
  | count + 1 => 3 + width count

lemma width_eq (count : Nat) : width count = count * 3 := by
  induction count with
  | zero => rfl
  | succ count ih => rw [width, ih]; omega

/-- All original three-system blocks, with distinct consecutive physical identities. -/
public abbrev layout (count : Nat) :=
  (QuantumSignature.qubits (width count)).canonicalPlacement.layout

/-- Alice's two actual measured values for every block. -/
public abbrev resultShape (count : Nat) : CShape :=
  .fixedVector count (.product (.finite 2) (.finite 2))

/-- The unknown systems and shared Bell resources are all supplied quantum systems. -/
def quantumContext (count : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨0⟩ (layout count) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

/-- Every supplied quantum system and every written classical result remains live. -/
public def context (count : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (quantumContext count) 2 (count * 2)

lemma context_wires (count : Nat) :
    (layout count).wires = (context count).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, context, MeasurementCells.context_quantumWires]
  change (layout count).wires = (layout count).wires ++ []
  exact (List.append_nil _).symm

/-- Correspondence of complete wire records, including physical identity and dimension. -/
def position (count : Nat) : Fin (width count) ≃ Fin (context count).systemCount :=
  positionsOfEqualWires _ _ (context_wires count)

lemma position_dimension (count : Nat) (index : Fin (width count)) :
    ((context count).quantumLayout.wire (position count index)).dimension = 2 := by
  rw [position, wireAtCorrespondingPosition]
  rfl

/-- Original block and local system determine the actual physical position. -/
def wireIndex {count : Nat} (block : Fin count) (side : Fin 3) : Fin (width count) :=
  Fin.cast (width_eq count).symm (finProdFinEquiv (block, side))

/-- Two separate binary cells per block, each written by its own measurement. -/
public def resultCell (count : Nat) (index : Fin (count * 2)) :
    CWriteRef (context count) (.finite 2) :=
  MeasurementCells.reference (quantumContext count) 2 (count * 2) index

lemma resultCell_key_injective (count : Nat) :
    Function.Injective (fun index => (resultCell count index).key) :=
  MeasurementCells.reference_key_injective (quantumContext count) 2 (count * 2)

/-- Structural read of both actual stored values, in Alice's measurement order. -/
public def resultInput (count : Nat) : CInputRef (context count) (resultShape count) :=
  .fixedVector fun block => .product
    (.storage (resultCell count (finProdFinEquiv (block, 0))).toCStorageRef)
    (.storage (resultCell count (finProdFinEquiv (block, 1))).toCStorageRef)

/-- Only Alice's first two systems in each block are measured. -/
def measuredPosition (count : Nat) (index : Fin (count * 2)) :
    Fin (context count).systemCount :=
  position count (wireIndex (finProdFinEquiv.symm index).1
    ((finProdFinEquiv.symm index).2.castLE (by decide)))

lemma measuredPosition_dimension (count : Nat) (index : Fin (count * 2)) :
    ((context count).quantumLayout.wire (measuredPosition count index)).dimension = 2 :=
  position_dimension count _

/-- Actual measurement order follows block order and then Alice's two local positions. -/
public def readouts (count : Nat) : List (ZReadout (context count)) :=
  QubitReadouts.readouts (measuredPosition count) (measuredPosition_dimension count)
    (resultCell count)

end

end QuantumAlg.QuantumTeleportation.Parallel
