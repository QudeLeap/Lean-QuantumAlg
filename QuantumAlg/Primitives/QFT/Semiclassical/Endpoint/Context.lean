/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.SemiclassicalFourier
public import QuantumAlg.Core.Execution.Measurement.Cells
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Base.Layout.Qubit.Quantum
public import QuantumAlg.Core.Execution.Context.Layout
public import QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BitReverse

/-!
# Physical interface and actual output cells for semiclassical Fourier readout

The input register is supplied and mutable. Exactly one fresh retained binary
cell is allocated for each measured physical wire. The output is a structural
vector of those existing cells; interpreting its reversed Fourier-frequency
order is a mathematical definition, with no packing operation or extra storage.
[GN96, 9511007.tex:214-244]
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

open Execution

noncomputable section

/-- Only native algorithm gates and the empty oracle interface are used. -/
public abbrev model : ExecutionModel := .quantum SemiclassicalFourierGate.model .empty

/-- Logical positions refer to the same physical systems throughout execution. -/
public def qubitLayout (n : Nat) : QubitLayout n :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

/-- Every input system has dimension two. -/
public def bankLayout (n : Nat) : QuantumLayout n := (qubitLayout n).toQuantumLayout

/-- A supplied register may change while remaining resident and requiring no auxiliary qubits. -/
@[reducible] public def inputContext (n : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨0⟩ (bankLayout n) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

/-- The output keeps the supplied register and all n actual measurement cells. -/
@[reducible] public def outputContext (n : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (inputContext n) 2 n

/-- Input coordinates follow the physical bank's complete ordered wire list. -/
public lemma qftSemiclassical_input_wires (n : Nat) :
    (bankLayout n).wires = (inputContext n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (bankLayout n).wires = (bankLayout n).wires ++ []
  exact (List.append_nil _).symm

/-- Retaining binary cells neither changes nor reorders the quantum bank. -/
public lemma qftSemiclassical_output_wires (n : Nat) :
    (bankLayout n).wires = (outputContext n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  unfold outputContext
  rw [MeasurementCells.context_quantumWires]
  change (bankLayout n).wires = (bankLayout n).wires ++ []
  exact (List.append_nil _).symm

/-- The same physical position denotes each measured wire after classical allocation. -/
public def wires (n : Nat) : Fin n ↪ Fin (outputContext n).systemCount :=
  (positionsOfEqualWires (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n)).toEmbedding

/-- Each selected actual wire retains its dimension-two certificate. -/
public lemma qftSemiclassical_wires_qubits (n : Nat) (i : Fin n) :
    ((outputContext n).quantumLayout.wire (wires n i)).dimension = 2 := by
  have same := wireAtCorrespondingPosition (bankLayout n)
    (outputContext n).quantumLayout (qftSemiclassical_output_wires n) i
  change ((outputContext n).quantumLayout.wire
    (positionsOfEqualWires _ _ (qftSemiclassical_output_wires n) i)).dimension = 2
  rw [same]
  rfl

/-- The i-th wire writes to the i-th distinct freshly retained binary cell. -/
public def resultCell (n : Nat) (i : Fin n) :
    CWriteRef (outputContext n)
      (.finite ((outputContext n).quantumLayout.wire (wires n i)).dimension) := by
  rw [qftSemiclassical_wires_qubits]
  exact MeasurementCells.reference (inputContext n) 2 n i

/-- Observe the actual binary cells without creating or computing another runtime value. -/
public def resultRead (n : Nat) :
    OutputRead (outputContext n) (.fixedVector n (.finite 2)) :=
  .read (.fixedVector fun i =>
    .storage (MeasurementCells.reference (inputContext n) 2 n i).toCStorageRef)

/-- The complete output lists the input bank and every retained measurement cell. -/
public def output (n : Nat) : Output (outputContext n) (.fixedVector n (.finite 2)) :=
  Output.all (outputContext n) (resultRead n)

/-- Basis-coordinate conversion induced by equality of the real ordered input wires. -/
public def inputBasisEquiv (n : Nat) : (inputContext n).register.Index ≃ Fin (2 ^ n) :=
  (basisOfEqualWires (bankLayout n) (inputContext n).quantumLayout
    (qftSemiclassical_input_wires n)).symm.trans (qubitLayout n).binaryIndexEquiv

/-- The output bank has the same big-endian physical basis coordinates. -/
public def outputBasisEquiv (n : Nat) : (outputContext n).register.Index ≃ Fin (2 ^ n) :=
  (basisOfEqualWires (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n)).symm.trans (qubitLayout n).binaryIndexEquiv

/-- Extract one finite binary value as a mathematical bit label. -/
public def binaryValue (value : CShape.Value (.finite 2)) : Fin 2 :=
  match value with
  | .finite bit => bit

/-- Interpret the stored physical wire-order vector as that bank's basis label. -/
public def physicalLabel (n : Nat)
    (value : CShape.Value (.fixedVector n (.finite 2))) : Fin (2 ^ n) :=
  match value with
  | .fixedVector entries =>
      (qubitLayout n).binaryIndexEquiv (fun i => binaryValue (entries i))

/-- The first stored outcome is the least significant frequency bit. This computes no circuit. -/
public def frequency (n : Nat)
    (value : CShape.Value (.fixedVector n (.finite 2))) : Fin (2 ^ n) :=
  qftReverseBits n (physicalLabel n value)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
