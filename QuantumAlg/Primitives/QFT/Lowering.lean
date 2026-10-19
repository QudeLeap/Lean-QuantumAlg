/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Components.GateModel.Fourier
public import QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.Swap

/-!
# Verified lowering of native Fourier gates

Every original occurrence is replaced on precisely its original physical
wires. The full matrix is preserved, so arbitrary states, entanglement with
spectators, and global phase are preserved as well. Sequential and disjoint
parallel circuit structure is retained by the generic refinement operation.
-/

namespace QuantumAlg.QuantumFourierTransform.Lowering
noncomputable section

/-- One standard-model Hadamard realizes the source token exactly. -/
public def hadamardRealization (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles
      (FourierGate.signature .hadamard).canonicalPlacement.layout
      (fun _ => FourierGate.operator .hadamard) where
  circuit := .macroCall "hadamard"
    (.native (GateModel.Application.canonical AlgorithmGate.model (.singleQubit Gate.HOp)))
  matrix_eq := by
    intro environment
    rw [UnitaryCircuit.macroCall_matrix, UnitaryCircuit.native_matrix,
      GateModel.Application.gateApplication_canonical_operator]
    rfl

/-- The exact local implementation of each source instruction. -/
public def localRealization (oracles : OracleModel) (token : FourierGate.Token) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles
      (FourierGate.signature token).canonicalPlacement.layout
      (fun _ => FourierGate.operator token) :=
  match token with
  | .hadamard => hadamardRealization oracles
  | .controlledPhase angle => Gate.ControlledPhase.realization oracles angle
  | .swap => Gate.Swap.realization oracles

/-- Relocate each local word to the source occurrence, preserving all spectators. -/
public def nativeRealization (oracles : OracleModel) {count : Nat}
    {layout : QuantumLayout count} (application : GateModel.Application FourierGate.model layout) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles layout
      (fun _ => application.operator) :=
  UnitaryCircuit.realizeNativeApplication application
    (localRealization oracles application.occurrence.token)

/-- No oracle access is introduced when compiling the oracle-free QFT source. -/
public def instructions (oracles : OracleModel) :
    UnitaryCircuit.InstructionRealizations
      FourierGate.model .empty AlgorithmGate.model oracles where
  interpretation := fun _ => OracleModel.emptyInterpretation
  native := nativeRealization oracles
  query application := False.elim
    (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

/-- Compile the same source construction into the requested standard-model environment. -/
public def lower (oracles : OracleModel) {count : Nat} {layout : QuantumLayout count}
    (source : UnitaryCircuit FourierGate.model .empty layout) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  source.refine (instructions oracles)

/-- Exact operator preservation for every layout and every source circuit shape. -/
public lemma lower_matrix (oracles : OracleModel) {count : Nat} {layout : QuantumLayout count}
    (source : UnitaryCircuit FourierGate.model .empty layout)
    (environment : oracles.Interpretation) :
    (lower oracles source).matrix environment = source.matrix OracleModel.emptyInterpretation :=
  UnitaryCircuit.refine_matrix source (instructions oracles) environment

end
end QuantumAlg.QuantumFourierTransform.Lowering
