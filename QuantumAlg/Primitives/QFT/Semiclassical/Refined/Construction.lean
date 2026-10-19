/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SemiclassicalFourier
public import QuantumAlg.Primitives.QFT.Semiclassical.Construction
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Components.Gates.SemiclassicalFourier
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Store

/-!
# Separately counted native semiclassical Fourier schedule

This is the same actual Hadamard, measurement, stored-result branch and
single-qubit feedback schedule as the default-model construction. The native
language separately counts Hadamards and parameterized phases, so its public
problem can bound each kind independently [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Refined

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The first count real feedback phases in their original source order. -/
public def phasePrefix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    (count : Nat) → count ≤ n →
      UnitaryCircuit SemiclassicalFourierGate.model .empty ctx.quantumLayout
  | 0, _ => UnitaryCircuit.identity SemiclassicalFourierGate.model .empty ctx.quantumLayout
  | count + 1, bounded =>
      (phasePrefix inverse wires qubits count (Nat.le_of_succ_le bounded)).seq
        (SemiclassicalFourierGate.phaseAt ctx.quantumLayout .empty
          (signedPhaseAngle inverse count) (wires ⟨count, Nat.lt_of_succ_le bounded⟩)
          (qubits ⟨count, Nat.lt_of_succ_le bounded⟩))

/-- All separately counted native phases selected by one real measured head bit. -/
public def phaseLayer (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    UnitaryCircuit SemiclassicalFourierGate.model .empty ctx.quantumLayout :=
  phasePrefix inverse wires qubits n le_rfl

/-- Read one actual finite result: one selects the full phase word and zero selects identity. -/
public def selectedPhase (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (value : CShape.Value (.finite dimension)) :
    UnitaryCircuit SemiclassicalFourierGate.model .empty ctx.quantumLayout :=
  match value with
  | .finite bit => if bit.val = 1 then phaseLayer inverse wires qubits
      else UnitaryCircuit.identity SemiclassicalFourierGate.model .empty ctx.quantumLayout

/-- The branch reads the same actual cell that the immediately preceding measurement wrote. -/
public def feedbackCode (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (result : CWriteRef ctx (.finite dimension)) :
    Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
  .branch (.storage result.toCStorageRef)
    (fun value => .unitary (selectedPhase inverse wires qubits value))

/-- The entire native adaptive schedule, with exactly the original physical wire order. -/
public def code (inverse : Bool) :
    (n : Nat) → (wires : Fin n ↪ Fin ctx.systemCount) →
      (∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) →
      (∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension)) →
      Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false
  | 0, _, _, _ =>
      Circuit.id (model := .quantum SemiclassicalFourierGate.model .empty)
        (allowAllocation := false) ctx
  | n + 1, wires, qubits, outputs =>
      let tailWires : Fin n ↪ Fin ctx.systemCount :=
        ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
      let tailQubits := fun i : Fin n => qubits i.succ
      let hadamard : Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
        .unitary (SemiclassicalFourierGate.hadamardAt ctx.quantumLayout .empty
          (wires 0) (qubits 0))
      let measured : Circuit (.quantum SemiclassicalFourierGate.model .empty) ctx ctx false :=
        .measureZ (wires 0) (outputs 0)
      hadamard.seq
        (measured.seq
          ((feedbackCode inverse tailWires tailQubits (outputs 0)).seq
            (code inverse n tailWires tailQubits (fun i => outputs i.succ))))

/-- Refining the phase labels preserves the exact complete-layout operator of each prefix. -/
public lemma qftSemiclassical_refinedPhasePrefix_matrix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (count : Nat) (bounded : count ≤ n) {environment : OracleModel.empty.Interpretation} :
    ((phasePrefix inverse wires qubits count bounded).matrix environment) =
      ((Semiclassical.phasePrefix inverse wires qubits count bounded).matrix environment) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [phasePrefix, Semiclassical.phasePrefix, UnitaryCircuit.seq_matrix,
        SemiclassicalFourierGate.semiclassicalFourier_phaseAt_matrix, ih]

/-- The actual value-selected word has exactly the original full-layout operator. -/
public lemma qftSemiclassical_refinedSelectedPhase_matrix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    {dimension : ℕ+} (value : CShape.Value (.finite dimension)) {environment :
      OracleModel.empty.Interpretation} :
    ((selectedPhase inverse wires qubits value).matrix environment) =
      ((Semiclassical.selectedPhase inverse wires qubits value).matrix environment) := by
  cases value with
  | finite bit =>
      simp only [selectedPhase, Semiclassical.selectedPhase]
      split_ifs
      · exact qftSemiclassical_refinedPhasePrefix_matrix inverse wires qubits n le_rfl
      · rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Refined
