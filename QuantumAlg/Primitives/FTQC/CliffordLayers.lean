/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Identities
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
public import QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.WireAddress
import all QuantumAlg.Components.QubitPrimitive.Placement
import all QuantumAlg.Components.QubitPrimitive.Word
import all QuantumAlg.Components.GateModel.CliffordT
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import Mathlib.Tactic

/-!
# Parallel Clifford+T layers on fixed qubit interfaces

Tensor nodes preserve parallel execution in the sealed circuit. T-depth is
computed from these nodes, rather than counted from a flattened gate list.
-/

public section

namespace QuantumAlg.FTQC

open CliffordT UnitaryCircuit Gate

noncomputable section

/-- Canonical physical interface for strict Clifford+T constructions. -/
abbrev CliffordCircuit (oracles : OracleModel) (width : Nat) :=
  UnitaryCircuit CliffordTGate.model oracles
    (QuantumSignature.qubits width).canonicalPlacement.layout

/-- Two simultaneous words on disjoint canonical physical wires. -/
def layer2 (oracles : OracleModel) (a b : List Letter) : CliffordCircuit oracles 2 :=
  parallelBinary (ofWord oracles a) (ofWord oracles b)

/-- Three simultaneous words on disjoint canonical physical wires. -/
def layer3 (oracles : OracleModel) (a b c : List Letter) : CliffordCircuit oracles 3 :=
  parallelBinary (layer2 oracles a b) (ofWord oracles c)

/-- The strict model's CNOT, applied to the actual distinct argument positions. -/
def cx (oracles : OracleModel) {n : Nat} (a b : Fin n) (h : a ≠ b) :
    CliffordCircuit oracles n :=
  native (GateModel.Application.ofPositions CliffordTGate.model .cnot
    (QuantumSignature.qubits n).canonicalPlacement.layout
    ⟨![a, b], by intro left right same; fin_cases left <;> fin_cases right <;> simp_all⟩
    (fun _ => rfl))

/-- Sequence blocks without flattening their physical parallel structure. -/
def blocks {oracles : OracleModel} {n : Nat} (cs : List (CliffordCircuit oracles n)) :
    CliffordCircuit oracles n :=
  sequenceList (identity CliffordTGate.model oracles
    (QuantumSignature.qubits n).canonicalPlacement.layout) cs

/-- Duration assignment measuring sequential strict-model T stages. -/
def tDuration (oracles : OracleModel)
    (event : Resource.Event (.quantum CliffordTGate.model oracles)) : Nat :=
  if event = Letter.t.event oracles then 1 else 0

@[simp] lemma word_matrix (oracles : OracleModel) (environment : oracles.Interpretation)
    (word : List Letter) : (ofWord oracles word).binaryMatrix environment = evalOp word := by
  unfold binaryMatrix
  rw [ofWord_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 1).symm (evalOp word)

private lemma sequenceList_matrix_unitary {oracles : OracleModel} {n : Nat}
    (cs : List (CliffordCircuit oracles n)) (start : CliffordCircuit oracles n)
    (environment : oracles.Interpretation) :
    (sequenceList start cs).binaryMatrix environment =
      cs.foldl (fun acc circuit => circuit.binaryMatrix environment * acc)
        (start.binaryMatrix environment) := by
  induction cs generalizing start with
  | nil => rfl
  | cons circuit cs ih =>
      change (sequenceList (seq start circuit) cs).binaryMatrix environment = _
      rw [ih, unitaryCircuit_binaryMatrix_seq]
      rfl

/-- Exact binary-coordinate semantics of the actual block sequence. -/
@[simp] lemma blocks_matrix {oracles : OracleModel} {n : Nat}
    (cs : List (CliffordCircuit oracles n)) (environment : oracles.Interpretation) :
    (blocks cs).binaryMatrix environment =
      cs.foldl (fun acc circuit => circuit.binaryMatrix environment * acc) 1 := by
  unfold blocks
  rw [sequenceList_matrix_unitary, unitaryCircuit_binaryMatrix_identity]

@[simp] lemma layer2_matrix (oracles : OracleModel) (a b : List Letter)
    (environment : oracles.Interpretation) :
    (layer2 oracles a b).binaryMatrix environment = (evalOp a).tensor (evalOp b) := by
  simp only [layer2, parallelBinary_binaryMatrix, word_matrix]

@[simp] lemma layer3_matrix (oracles : OracleModel) (a b c : List Letter)
    (environment : oracles.Interpretation) :
    (layer3 oracles a b c).binaryMatrix environment =
      ((evalOp a).tensor (evalOp b)).tensor (evalOp c) := by
  simp only [layer3, parallelBinary_binaryMatrix, layer2_matrix, word_matrix]

@[simp] lemma cx_matrix (oracles : OracleModel) {n : Nat} (a b : Fin n) (h : a ≠ b)
    (environment : oracles.Interpretation) :
    (cx oracles a b h).binaryMatrix environment = QubitPrimitive.operator (.cnot a b h) := by
  unfold binaryMatrix
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    (QubitPrimitive.nativeApplication (QubitLayout.canonical n) (.cnot a b h)).operator = _
  rw [QubitPrimitive.nativeApplication_operator]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm _

/-- Recover the physical operator from the exact binary-coordinate view. -/
lemma matrix_of_binaryMatrix_eq {oracles : OracleModel} {n : Nat}
    (circuit : CliffordCircuit oracles n) (operator : UnitaryOperator (Qubits n))
    (environment : oracles.Interpretation)
    (equal : circuit.binaryMatrix environment = operator) :
    circuit.matrix environment =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm operator := by
  rw [← equal]
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n) (circuit.matrix environment)).symm

private lemma sumQubits1 (n : Nat) (f : (Qubits n).Index → ℂ) (h : n = 1) :
    ∑ i, f i = f 0 + f 1 := by
  subst n
  exact Fin.sum_univ_two f

private lemma sumQubits2 (n : Nat) (f : (Qubits n).Index → ℂ) (h : n = 2) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  subst n
  exact Fin.sum_univ_four f

private lemma sumQubits3 (n : Nat) (f : (Qubits n).Index → ℂ) (h : n = 3) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  subst n
  exact Fin.sum_univ_eight f

private lemma tensor_diagonal {m n : Nat}
    [DecidableEq (Qubits m).Index] [DecidableEq (Qubits n).Index]
    (a : (Qubits m).Index → ℂ) (b : (Qubits n).Index → ℂ) :
    HilbertOperator.tensor (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun i => a (prodEquiv.symm i).1 * b (prodEquiv.symm i).2) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [HilbertOperator.tensor_apply, Matrix.diagonal_apply, ite_true]
  · by_cases h₁ : (prodEquiv.symm i).1 = (prodEquiv.symm j).1
    · by_cases h₂ : (prodEquiv.symm i).2 = (prodEquiv.symm j).2
      · exact (h (prodEquiv.symm.injective (Prod.ext h₁ h₂))).elim
      · simp [HilbertOperator.tensor_apply, h, h₁, h₂]
    · simp [HilbertOperator.tensor_apply, Matrix.diagonal_apply, h, h₁]

end

end QuantumAlg.FTQC
