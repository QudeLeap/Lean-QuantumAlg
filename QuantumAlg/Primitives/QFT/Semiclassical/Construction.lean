/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.PhaseOperator
public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Primitives.QFT.Source

/-!
# Native measurement and stored-result feedback for the Fourier recursion

Each stage applies an actual Hadamard, measures its physical wire into the
supplied writable cell, and reads that same cell before selecting the actual
single-qubit phase gates. The tail continues on the remaining physical wires.
The code allocates nothing and does not reverse or reset the measured bank.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- A sign choice changes the physical rotations, leaving the recursion order fixed. -/
public def signedPhaseAngle (inverse : Bool) (offset : Nat) : Real :=
  if inverse then -(Source.phaseAngle offset) else Source.phaseAngle offset

/-- The first `count` actual single-qubit feedback gates, in source order. -/
public def phasePrefix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    (count : Nat) → count ≤ n →
      UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model .empty ctx.quantumLayout
  | count + 1, bounded =>
      (phasePrefix inverse wires qubits count (Nat.le_of_succ_le bounded)).seq
        (Gate.singleQubitAt ctx.quantumLayout .empty
          (phaseGateOp (signedPhaseAngle inverse count))
          (wires ⟨count, Nat.lt_of_succ_le bounded⟩)
          (qubits ⟨count, Nat.lt_of_succ_le bounded⟩))

/-- All rotations selected by one measured head bit; none is an uncharged matrix callback. -/
public def phaseLayer (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  phasePrefix inverse wires qubits n le_rfl

/-- The finite stored value selects either the full native phase word or the empty word. -/
public def selectedPhase (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (value : CShape.Value (.finite dimension)) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  match value with
  | .finite bit => if bit.val = 1 then phaseLayer inverse wires qubits
      else UnitaryCircuit.identity AlgorithmGate.model .empty ctx.quantumLayout

/-- Read the actual written measurement cell before selecting its physical phase gates. -/
public def feedbackCode (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (result : CWriteRef ctx (.finite dimension)) :
    Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
  .branch (.storage result.toCStorageRef)
    (fun value => .unitary (selectedPhase inverse wires qubits value))

/-- The real stored value selects the exact joint operator on the bank and reference. -/
public lemma qftSemiclassical_feedbackCode_actual_reference
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    (inverse : Bool) {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (result : CWriteRef ctx (.finite dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (((feedbackCode inverse wires qubits result).execute environment)
      Reference state).quantumMarginal =
      (state.applyUnitary (fun entry => UnitaryOperator.prodTensor
        ((selectedPhase inverse wires qubits
          (entry.1.read (.storage result.toCStorageRef))).matrix environment.quantum)
        (1 : UnitaryOperator Reference))).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal (.storage result.toCStorageRef)
    (selectedPhase inverse wires qubits) environment state

/-- The complete native adaptive schedule on an existing bank and its writable outcome cells. -/
public def code (inverse : Bool) :
    (n : Nat) → (wires : Fin n ↪ Fin ctx.systemCount) →
      (∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) →
      (∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension)) →
      Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false
  | 0, _, _, _ =>
      Circuit.id (model := .quantum AlgorithmGate.model .empty) (allowAllocation := false) ctx
  | n + 1, wires, qubits, outputs =>
      let tailWires : Fin n ↪ Fin ctx.systemCount :=
        ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
      let tailQubits := fun i : Fin n => qubits i.succ
      let hadamard : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
        .unitary (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp
          (wires 0) (qubits 0))
      let measured : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
        .measureZ (wires 0) (outputs 0)
      hadamard.seq
        (measured.seq
          ((feedbackCode inverse tailWires tailQubits (outputs 0)).seq
            (code inverse n tailWires tailQubits (fun i => outputs i.succ))))

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
