/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic
public import QuantumAlg.Components.Gates.Hadamard.Layer
public import QuantumAlg.Components.Gates.OpenControl.Semantics
public import QuantumAlg.Components.Gates.SingleQubit.Singleton
public import QuantumAlg.Components.QubitPrimitive
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Wire
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic
import all QuantumAlg.Components.Gates.OpenControl.Semantics
import all QuantumAlg.Components.Gates.SingleQubit.Singleton
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Wire

/-!
# Intrinsic native range preparation

The Shukla--Vedula word only touches qubits through the highest set bit of the
known order.  This module constructs that literal intrinsic word.  Endpoint
registers can add an untouched high prefix with binary suffix placement.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation.Intrinsic

noncomputable section

open scoped BigOperators

variable {N : Nat}

/-- Smallest binary width containing every set bit of the expansion. -/
@[expose, implicit_reducible] public def width (expansion : OrderExpansion N) : Nat :=
  expansion.last + 1

@[simp] public theorem width_asOrderExpansion
    (expansion : OrderExpansion.PositiveGapExpansion N) :
    width expansion.asOrderExpansion = expansion.width := by
  simp [width, OrderExpansion.PositiveGapExpansion.width]

/-- Every set-bit exponent lies in the intrinsic register. -/
public theorem ell_lt_width (expansion : OrderExpansion N)
    (index : Fin expansion.count) : expansion.ell index < width expansion := by
  unfold width OrderExpansion.last
  have lastBound : 0 < expansion.count := expansion.count_pos
  let last : Fin expansion.count := ⟨expansion.count - 1, by omega⟩
  have indexLe : index ≤ last := by
    apply Fin.mk_le_mk.mpr
    omega
  have upper := expansion.ell_strict.monotone indexLe
  exact Nat.lt_succ_of_le upper

/-- Canonical intrinsic binary layout. -/
public abbrev layout (expansion : OrderExpansion N) : QuantumLayout (width expansion) :=
  (QuantumSignature.qubits (width expansion)).canonicalPlacement.layout

/-- Physical wire carrying one set-bit exponent. -/
public def wire (expansion : OrderExpansion N) (index : Fin expansion.count) :
    Fin (width expansion) :=
  WireAddress.littleEndianWire ⟨expansion.ell index, ell_lt_width expansion index⟩

/-- Physical wire carrying an arbitrary intrinsic logical bit. -/
public def logicalWire (expansion : OrderExpansion N)
    (bit : Fin (width expansion)) : Fin (width expansion) :=
  WireAddress.littleEndianWire bit

@[simp] public theorem wire_val (expansion : OrderExpansion N)
    (index : Fin expansion.count) :
    (wire expansion index).val = width expansion - 1 - expansion.ell index := by
  rfl

@[simp] public theorem logicalWire_val (expansion : OrderExpansion N)
    (bit : Fin (width expansion)) :
    (logicalWire expansion bit).val = width expansion - 1 - bit.val := by
  rfl

/-- Intrinsic target bit at one offset in a source gap. -/
public def gapBit (expansion : OrderExpansion N) (gap : Fin expansion.gaps)
    (offset : Fin (OrderPreparation.gapWidth expansion gap)) :
    Fin (width expansion) :=
  ⟨expansion.ell (OrderPreparation.leftIndex expansion gap) + offset.val, by
    have strict := OrderPreparation.ell_left_lt_right expansion gap
    have offsetBound := offset.isLt
    have upper := ell_lt_width expansion (OrderPreparation.rightIndex expansion gap)
    unfold OrderPreparation.gapWidth at offsetBound
    omega⟩

/-- The next source wire is physically earlier than the current source wire. -/
public theorem rightWire_lt_leftWire (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) :
    (wire expansion (OrderPreparation.rightIndex expansion gap)).val <
      (wire expansion (OrderPreparation.leftIndex expansion gap)).val := by
  rw [wire_val, wire_val]
  have upper := ell_lt_width expansion (OrderPreparation.rightIndex expansion gap)
  have strict := OrderPreparation.ell_left_lt_right expansion gap
  omega

/-- The next source wire is physically earlier than every bit in its gap. -/
public theorem rightWire_lt_gapWire (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps)
    (offset : Fin (OrderPreparation.gapWidth expansion gap)) :
    (wire expansion (OrderPreparation.rightIndex expansion gap)).val <
      (logicalWire expansion (gapBit expansion gap offset)).val := by
  rw [wire_val, logicalWire_val]
  have upper := ell_lt_width expansion (OrderPreparation.rightIndex expansion gap)
  have strict := OrderPreparation.ell_left_lt_right expansion gap
  have offsetBound := offset.isLt
  have targetBitLt :
      expansion.ell (OrderPreparation.leftIndex expansion gap) + offset.val <
        expansion.ell (OrderPreparation.rightIndex expansion gap) := by
    unfold OrderPreparation.gapWidth at offsetBound
    omega
  unfold gapBit OrderPreparation.gapWidth
  dsimp
  omega

/-- One literal native one-qubit word on the canonical singleton layout. -/
public def singleQubit (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits 1).canonicalPlacement.layout :=
  Gate.singleQubitAt
    (QuantumSignature.qubits 1).canonicalPlacement.layout oracles operator
      (0 : Fin 1) rfl

@[simp] public theorem singleQubit_binaryMatrix (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (singleQubit oracles operator).binaryMatrix = operator := by
  exact Gate.singleQubitAt_singleton_binaryMatrix oracles operator

/-- One native Pauli-X instruction at an intrinsic physical wire. -/
public def xAt (oracles : OracleModel) (expansion : OrderExpansion N)
    (target : Fin (width expansion)) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  QubitPrimitive.circuit (.x target)
    (QubitLayout.canonical (width expansion)) oracles

/-- One native Y rotation at an intrinsic physical wire. -/
public def rotYAt (oracles : OracleModel) (expansion : OrderExpansion N)
    (target : Fin (width expansion)) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  UnitaryCircuit.onBinaryWire target (singleQubit oracles (rotYOp angle))

/-- Initial X gates on every set bit except the lowest. -/
public def initialX (oracles : OracleModel) (expansion : OrderExpansion N) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  .indexedProduct "sv24-intrinsic-initial-x" expansion.gaps
    (.identity AlgorithmGate.model oracles (layout expansion))
    (fun gap => xAt oracles expansion
      (wire expansion (OrderPreparation.rightIndex expansion gap)))

/-- Parallel Hadamards below the lowest set bit. -/
public def lowHadamards (oracles : OracleModel) (expansion : OrderExpansion N) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  (UnitaryCircuit.onBinarySuffix (width expansion - expansion.first)
    (Gate.HadamardLayer.circuit oracles expansion.first)).castQubitWidth
      (Nat.sub_add_cancel (by
        exact Nat.le_of_lt
          (ell_lt_width expansion ⟨0, expansion.count_pos⟩)))

/-- Open-controlled Hadamards across one binary gap. -/
public def gapHadamards (oracles : OracleModel) (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  .indexedProduct "sv24-intrinsic-gap-hadamards"
    (OrderPreparation.gapWidth expansion gap)
    (.identity AlgorithmGate.model oracles (layout expansion))
    (fun offset =>
      UnitaryCircuit.onBinarySeparated
        (wire expansion (OrderPreparation.rightIndex expansion gap))
        (logicalWire expansion (gapBit expansion gap offset))
        (rightWire_lt_gapWire expansion gap offset)
        (Gate.OpenControl.hadamard oracles))

/-- One literal intrinsic source-gap stage. -/
public def gapStage (oracles : OracleModel) (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  let target := wire expansion (OrderPreparation.rightIndex expansion gap)
  let rotation := if gap.val = 0 then
      rotYAt oracles expansion target (OrderPreparation.sourceAngle expansion gap)
    else
      let control := wire expansion (OrderPreparation.leftIndex expansion gap)
      UnitaryCircuit.onBinarySeparated target control
        (rightWire_lt_leftWire expansion gap)
        (Gate.OpenControl.rotYRight oracles
          (OrderPreparation.sourceAngle expansion gap))
  rotation.seq (gapHadamards oracles expansion gap)

/-- Complete intrinsic native preparation schedule. -/
@[expose] public def circuit (oracles : OracleModel) (expansion : OrderExpansion N) :
    UnitaryCircuit AlgorithmGate.model oracles (layout expansion) :=
  .indexedProduct "sv24-intrinsic-gaps" expansion.gaps
    ((initialX oracles expansion).seq (lowHadamards oracles expansion))
    (gapStage oracles expansion)

end

end QuantumAlg.FiniteCyclicDLP.OrderPreparation.Intrinsic
