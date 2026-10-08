/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Model
public import QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Semantics
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Declared short-DLP group-operation query

One oracle declaration fixes the group, the faithful workspace encoding and
the reversible operation for every granted pair of public group elements.
A runtime call selects its pair and dimension-correct physical placement.
-/

namespace QuantumAlg.ShortDLP

noncomputable section

/-- The sole accounting coordinate granted by one fixed short-DLP declaration. -/
public inductive DeclaredCoordinate where
  | groupOperation
  deriving DecidableEq

/-- The declaration owns the complete query family. Runtime elements select
an instance; they never supply an independently constructed operator. -/
@[implicit_reducible]
public def declaredModel {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) : OracleModel where
  Query := (ZMod N)ˣ × (ZMod N)ˣ
  Coordinate := DeclaredCoordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (totalQubits params)
  operator pair :=
    UnitaryOperator.reindex
      (QuantumSignature.qubitsIndexEquiv (totalQubits params)).symm
      (oracleOperator encoding pair.1 pair.2)
  coordinate _ := .groupOperation

/-- One model-owned group-operation query on its complete canonical carrier. -/
def declaredCircuit (gates : GateModel) {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    UnitaryCircuit gates (declaredModel encoding)
      (QuantumSignature.qubits (totalQubits params)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (declaredModel encoding) (g, x)
    (QuantumSignature.qubits (totalQubits params)).canonicalPlacement)

/-- The same declared permutation determines the physical query matrix. -/
theorem declaredCircuit_matrix (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (declaredCircuit gates encoding g x).matrix =
      UnitaryOperator.reindex
        (QuantumSignature.qubitsIndexEquiv (totalQubits params)).symm
        (oracleOperator encoding g x) := by
  rw [declaredCircuit, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  apply Subtype.ext
  rfl

/-- In the source's binary coordinates the fixed query is exactly the reversible
group-operation permutation, including its original workspace labels. -/
theorem declaredCircuit_binaryMatrix (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (declaredCircuit gates encoding g x).binaryMatrix =
      oracleOperator encoding g x := by
  rw [UnitaryCircuit.binaryMatrix, declaredCircuit_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (totalQubits params)).symm
    (oracleOperator encoding g x)

/-- The actual model-owned query has the source permutation at each pair of
binary basis coordinates. -/
theorem declaredCircuit_binaryMatrix_entry (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (output input :
      (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) :
    (declaredCircuit gates encoding g x).binaryMatrix
        (tripleEquiv params output) (tripleEquiv params input) =
      if oraclePerm encoding g x output = input then 1 else 0 := by
  rw [declaredCircuit_binaryMatrix]
  exact oracleOperator_entry encoding g x output input

/-- The model-owned query acts on a source basis state by its explicit
reversible group-operation permutation. -/
theorem declaredCircuit_binaryMatrix_apply_ket (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (input :
      (Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) ×
        Fin (2 ^ params.workspaceBits)) :
    (declaredCircuit gates encoding g x).binaryMatrix.apply
        (NormalizedVector.ket (tripleEquiv params input)) =
      NormalizedVector.ket
        (tripleEquiv params (oraclePerm encoding g x input)) := by
  rw [declaredCircuit_binaryMatrix]
  exact oracleOperator_apply_ket encoding g x input

/-- The declared query contributes exactly one oracle event. -/
theorem declaredCircuit_eventCost (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (declaredCircuit gates encoding g x).eventCost =
      ResourcePool.singleton
        (model := .quantum gates (declaredModel encoding))
        (.oracle .groupOperation) := by
  rfl

/-- The abstract declared query occupies one dependency step. -/
theorem declaredCircuit_unitDepth (gates : GateModel) {N : Nat}
    {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (declaredCircuit gates encoding g x).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

end

end QuantumAlg.ShortDLP
