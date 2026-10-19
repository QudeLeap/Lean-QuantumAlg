/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.GateModel.Algorithm.Permutation
public import QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
public import QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact SWAP from three actual native CNOT applications

The target exchanges the two computational-basis coordinates independently of
the implementation. The default-model construction uses CNOT in the forward,
backward and forward directions. Its macro annotation retains this entire
expansion and therefore its native events and sequential dependency depth.
-/

namespace QuantumAlg.Gate.Swap

noncomputable section

/-- The two physical qubits on which the local construction runs. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The independent two-qubit exchange permutation, in the fixed big-endian basis. -/
@[expose]
public def permutation : Equiv.Perm layout.Basis :=
  ((QuantumSignature.qubitsIndexEquiv 2).trans (Equiv.swap 1 2)).trans
    (QuantumSignature.qubitsIndexEquiv 2).symm

/-- The target exchanges both values, without an assumption on either input. -/
public lemma swap_permutation_pair (left right : Fin 2) :
    permutation ![left, right] = ![right, left] := by
  fin_cases left <;> fin_cases right
  all_goals
    funext index
    fin_cases index <;> rfl

/-- The target acts coherently by exchanging the two basis coordinates. -/
@[expose]
public def operator : UnitaryOperator layout.register := UnitaryOperator.ofPerm permutation

private abbrev backward : GateModel.Application AlgorithmGate.model layout :=
  cnotApplication layout 1 0 (by decide) rfl rfl

private def backwardPermutation : Equiv.Perm layout.Basis :=
  backward.liftPermutation AlgorithmGate.cnotPermutation

private lemma backward_pair (left right : Fin 2) :
    backwardPermutation ![left, right] = ![left + right, right] := by
  apply (backward.liftPermutation_eq_iff AlgorithmGate.cnotPermutation _ _).mpr
  constructor
  · have selected (first second : Fin 2) :
        (backward.basisEquiv ![first, second]).1 = ![second, first] := by
      funext index
      fin_cases index <;> apply Fin.ext <;> rfl
    have action := AlgorithmGate.cnotPermutation_pair right left
    rw [add_comm right left] at action
    exact ((congrArg AlgorithmGate.cnotPermutation (selected left right)).trans action).trans
      (selected (left + right) right).symm
  · funext position
    have covered (index : Fin 2) : index ∈ backward.embedding.selection := by
      fin_cases index <;> decide
    exact False.elim ((Finset.mem_compl.mp position.property) (covered position.val))

private lemma native_permutation_word :
    (AlgorithmGate.cnotPermutation.trans backwardPermutation).trans
      AlgorithmGate.cnotPermutation = permutation := by
  have pair (left right : Fin 2) :
      AlgorithmGate.cnotPermutation
        (backwardPermutation (AlgorithmGate.cnotPermutation ![left, right])) =
          permutation ![left, right] := by
    rw [AlgorithmGate.cnotPermutation_pair, backward_pair,
      AlgorithmGate.cnotPermutation_pair, swap_permutation_pair]
    fin_cases left <;> fin_cases right <;> rfl
  apply Equiv.ext
  intro basis
  have coordinates : basis = ![basis (0 : Fin 2), basis (1 : Fin 2)] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates]
  change AlgorithmGate.cnotPermutation
    (backwardPermutation (AlgorithmGate.cnotPermutation
      ![basis (0 : Fin 2), basis (1 : Fin 2)])) = _
  exact pair _ _

/-- Execute the full forward/backward/forward CNOT word as one descriptive macro. -/
public def circuit (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout :=
  let forward : UnitaryCircuit AlgorithmGate.model oracles layout :=
    UnitaryCircuit.native (GateModel.Application.canonical AlgorithmGate.model .cnot)
  UnitaryCircuit.macroCall "swap"
    ((forward.seq (UnitaryCircuit.native backward)).seq forward)

/-- The three actual CNOTs realize the independent SWAP operator with exact phase. -/
public lemma swap_circuit_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((circuit oracles).matrix environment) = operator := by
  simp only [circuit, UnitaryCircuit.macroCall_matrix, UnitaryCircuit.seq_matrix,
    UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator,
    AlgorithmGate.cnot_operator_ofPerm,
    backward.operator_ofPerm AlgorithmGate.cnotPermutation AlgorithmGate.cnot_operator_ofPerm]
  simp only [UnitaryOperator.ofPerm_mul]
  exact congrArg UnitaryOperator.ofPerm native_permutation_word

/-- The native realization records its actual target-language implementation. -/
public def realization (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles layout (fun _ => operator) where
  circuit := circuit oracles
  matrix_eq := swap_circuit_matrix oracles

/-- Every event is one of the three actual CNOT occurrences in execution order. -/
public lemma swap_circuit_events (oracles : OracleModel) :
    (circuit oracles).eventTrace = [.gate .cnot, .gate .cnot, .gate .cnot] := by rfl

/-- The three CNOTs share physical wires and contribute three sequential unit-depth steps. -/
public lemma swap_circuit_unit_depth (oracles : OracleModel) :
    (circuit oracles).evaluatedEventDepth (fun _ => 1) = 3 := by rfl

/-- The descriptive SWAP annotation accompanies exactly one full expanded word. -/
public lemma swap_circuit_macro_count (oracles : OracleModel) :
    (circuit oracles).macroCount "swap" = 1 := by
  rfl

end

end QuantumAlg.Gate.Swap
