/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.GateModel.Algorithm.Permutation
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact controlled exchange from two CNOTs and one Toffoli

The leading wire controls exchange of the two trailing values. The actual
native word has no work system and acts correctly on every input, retaining
exact phase. Its independent target exchanges only binary labels five and six.
-/

namespace QuantumAlg.Gate.ControlledSwap

noncomputable section

/-- The original control and both targets occupy three distinct physical qubits. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 3 := (QuantumSignature.qubits 3).canonicalPlacement.layout

/-- Independently specified control-one exchange, in big-endian labels. -/
@[expose]
public def permutation : Equiv.Perm layout.Basis :=
  ((QuantumSignature.qubitsIndexEquiv 3).trans (Equiv.swap 5 6)).trans
    (QuantumSignature.qubitsIndexEquiv 3).symm

/-- The false control preserves both targets; the true control exchanges them. -/
public theorem controlledSwap_permutation_triple (control left right : Fin 2) :
    permutation ![control, left, right] =
      if control = 0 then ![control, left, right] else ![control, right, left] := by
  fin_cases control <;> fin_cases left <;> fin_cases right
  all_goals
    funext index
    fin_cases index <;> rfl

/-- Exact coherent target of the independent basis permutation. -/
@[expose]
public def operator : UnitaryOperator layout.register := UnitaryOperator.ofPerm permutation

private abbrev outer : GateModel.Application AlgorithmGate.model layout :=
  cnotApplication layout 2 1 (by decide) rfl rfl

private def outerPermutation : Equiv.Perm layout.Basis :=
  outer.liftPermutation AlgorithmGate.cnotPermutation

private theorem outer_triple (control left right : Fin 2) :
    outerPermutation ![control, left, right] = ![control, right + left, right] := by
  apply (outer.liftPermutation_eq_iff AlgorithmGate.cnotPermutation _ _).mpr
  constructor
  · have selected (first second third : Fin 2) :
        (outer.basisEquiv ![first, second, third]).1 = ![third, second] := by
      funext index
      fin_cases index <;> apply Fin.ext <;> rfl
    exact ((congrArg AlgorithmGate.cnotPermutation (selected control left right)).trans
      (AlgorithmGate.cnotPermutation_pair right left)).trans
        (selected control (right + left) right).symm
  · funext position
    have untouched : position.val = (0 : Fin 3) := by
      have outside := Finset.mem_compl.mp position.property
      have members : (1 : Fin 3) ∈ outer.embedding.selection ∧
          (2 : Fin 3) ∈ outer.embedding.selection := by decide
      rcases position with ⟨position, outsidePosition⟩
      fin_cases position
      · rfl
      · exact False.elim (outside members.1)
      · exact False.elim (outside members.2)
    change (![control, left, right] position.val) =
      (![control, right + left, right] position.val)
    rw [untouched]
    rfl

private theorem native_permutation_word :
    (outerPermutation.trans AlgorithmGate.toffoliPermutation).trans outerPermutation =
      permutation := by
  have triple (control left right : Fin 2) :
      outerPermutation (AlgorithmGate.toffoliPermutation
        (outerPermutation ![control, left, right])) = permutation ![control, left, right] := by
    rw [outer_triple, AlgorithmGate.toffoliPermutation_triple, outer_triple,
      controlledSwap_permutation_triple]
    fin_cases control <;> fin_cases left <;> fin_cases right <;> rfl
  apply Equiv.ext
  intro basis
  have coordinates : basis = ![basis (0 : Fin 3), basis (1 : Fin 3), basis (2 : Fin 3)] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates]
  exact triple _ _ _

/-- The actual expansion uses CNOT, Toffoli and CNOT on the same three original wires. -/
public def circuit (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout :=
  let boundary : UnitaryCircuit AlgorithmGate.model oracles layout := .native outer
  .macroCall "controlled-swap"
    ((boundary.seq (.native (GateModel.Application.canonical AlgorithmGate.model .toffoli))).seq
      boundary)

/-- Every native operation contributes its own exact phase-preserving permutation. -/
public theorem controlledSwap_circuit_matrix (oracles : OracleModel) :
    (circuit oracles).matrix = operator := by
  simp only [circuit, UnitaryCircuit.macroCall_matrix, UnitaryCircuit.seq_matrix,
    UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator,
    AlgorithmGate.toffoli_operator_ofPerm,
    outer.operator_ofPerm AlgorithmGate.cnotPermutation AlgorithmGate.cnot_operator_ofPerm]
  simp only [UnitaryOperator.ofPerm_mul]
  exact congrArg UnitaryOperator.ofPerm native_permutation_word

/-- Exact realization supplied by the actual native expansion. -/
public def realization (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles layout operator where
  circuit := circuit oracles
  matrix_eq := controlledSwap_circuit_matrix oracles

/-- The three-instruction expansion has two CNOT occurrences and one Toffoli occurrence. -/
public theorem controlledSwap_circuit_events (oracles : OracleModel) :
    (circuit oracles).eventTrace = [.gate .cnot, .gate .toffoli, .gate .cnot] := by rfl

/-- Shared physical targets make the actual native word three sequential steps. -/
public theorem controlledSwap_circuit_unit_depth (oracles : OracleModel) :
    (circuit oracles).evaluatedEventDepth (fun _ => 1) = 3 := by rfl

end

end QuantumAlg.Gate.ControlledSwap
