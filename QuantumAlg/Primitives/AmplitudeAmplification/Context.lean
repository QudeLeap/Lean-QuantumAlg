/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Reindex

/-!
# The actual prepared amplification register

The source and any selected helper are one joint owned quantum register.
Every physical identity and dimension is kept by the explicit binary
coordinate equivalence. Preparation starts from the empty runtime context.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- No quantum or classical runtime input is supplied. -/
@[reducible] public def pre : RuntimeCtx .quantum := RuntimeCtx.empty

theorem pre_systemCount : pre.systemCount = 0 := rfl

/-- Consecutive physical systems in source-then-helper order. -/
def qubitLayout (n k : Nat) : QubitLayout (totalQubits n k) :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

@[implicit_reducible]
def runtimeLayout (n k : Nat) : QuantumLayout (totalQubits n k) :=
  (qubitLayout n k).toQuantumLayout

theorem preparationFresh : (⟨0⟩ : StorageKey) ∉ pre.keys := by decide

theorem preparationDisjoint (n k : Nat) :
    List.Disjoint (runtimeLayout n k).identities pre.physicalIdx :=
  List.disjoint_nil_right _

/-- The complete owned source and helper register, retained after execution. -/
@[implicit_reducible] public def post (n k : Nat) : RuntimeCtx .quantum :=
  pre.addOwnedLayout ⟨0⟩ (runtimeLayout n k) preparationFresh (preparationDisjoint n k)

theorem post_quantumWires (n k : Nat) :
    (post n k).quantumWires = (runtimeLayout n k).wires := by
  change (runtimeLayout n k).wires ++ [] = _
  exact List.append_nil _

theorem post_physicalIdx (n k : Nat) :
    (post n k).physicalIdx = List.range (totalQubits n k) := by
  rw [RuntimeCtx.physicalIdx, post_quantumWires]
  change (List.ofFn fun index : Fin (totalQubits n k) =>
    (runtimeLayout n k).wire index).map QuantumWire.identity = _
  rw [List.map_ofFn]
  change (qubitLayout n k).systemIdx = _
  simp [qubitLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- The native canonical word and runtime context contain exactly the same ordered wire records. -/
theorem post_canonical_wires (n k : Nat) :
    (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout.wires =
      (post n k).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, post_quantumWires]
  rfl

/-- Exact physical values of the freshly prepared systems. -/
def preparedLayoutEquiv (n k : Nat) :
    (runtimeLayout n k).register.Index ≃ (post n k).register.Index :=
  Execution.preparedEmptyBasisEquiv pre ⟨0⟩ (runtimeLayout n k)
    preparationFresh (preparationDisjoint n k) pre_systemCount

/-- Big-endian labels of those same actual physical values. -/
def preparedBasisEquiv (n k : Nat) :
    (post n k).register.Index ≃ (Qubits (totalQubits n k)).Index :=
  (preparedLayoutEquiv n k).symm.trans (qubitLayout n k).binaryIndexEquiv

/-- One charged all-zero basis preparation of the source and helper together. -/
def inputPreparation (n k : Nat) : BasisPreparation (runtimeLayout n k) :=
  ⟨(qubitLayout n k).binaryIndexEquiv.symm (0 : Fin (2 ^ totalQubits n k))⟩

/-- The source preparation's complete mathematical input. -/
def preparedInput (n k : Nat) : NormalizedVector (Qubits (totalQubits n k)) :=
  NormalizedVector.ket (R := Qubits (totalQubits n k)) 0

theorem inputPreparation_density (n k : Nat) :
    (DensityOperator.ofPure (inputPreparation n k).normalized).reindex
      (S := (post n k).register) (preparedLayoutEquiv n k) =
        (DensityOperator.ofPure (preparedInput n k)).reindex
          (S := (post n k).register) (preparedBasisEquiv n k).symm := by
  have preparedEntry (basis : (runtimeLayout n k).register.Index) :
      (inputPreparation n k).normalized basis =
        preparedInput n k ((qubitLayout n k).binaryIndexEquiv basis) := by
    dsimp only [preparedInput]
    change NormalizedVector.ket
      ((qubitLayout n k).binaryIndexEquiv.symm (0 : Fin (2 ^ totalQubits n k))) basis =
        NormalizedVector.ket (R := Qubits (totalQubits n k))
          (0 : Fin (2 ^ totalQubits n k)) _
    rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
    simp only [Equiv.eq_symm_apply]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix, preparedEntry, preparedEntry]
  rfl

end

end QuantumAlg.AmplitudeAmplification
