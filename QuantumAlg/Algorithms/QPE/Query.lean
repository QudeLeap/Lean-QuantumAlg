/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Granted controlled source queries at the QPE stage wires

Stage k executes the granted controlled source query 2^k times. Its control is
the corresponding little-endian phase bit in the original big-endian physical
word, and the source systems follow the phase register
[Lin22, phaseestimation.tex:514-523]. No controlled access is inferred from U.
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- The stage control followed by the original source systems, with no repeated position. -/
public def sourcePositions {phaseWidth : Nat} (systemWidth : Nat) (stage : Fin phaseWidth) :
    Fin (1 + systemWidth) ↪ Fin (phaseWidth + systemWidth) where
  toFun := Fin.addCases (fun _ : Fin 1 => Fin.castAdd systemWidth stage.rev)
    (Fin.natAdd phaseWidth)
  inj' := by
    intro left right same
    revert same
    refine Fin.addCases (fun first => ?_) (fun first => ?_) left
    · refine Fin.addCases (fun second => ?_) (fun second => ?_) right
      · intro _
        exact congrArg (Fin.castAdd systemWidth) (Subsingleton.elim first second)
      · intro same
        have values := congrArg Fin.val same
        simp only [Fin.addCases_left, Fin.addCases_right,
          Fin.val_castAdd, Fin.val_natAdd] at values
        omega
    · refine Fin.addCases (fun second => ?_) (fun second => ?_) right
      · intro same
        have values := congrArg Fin.val same
        simp only [Fin.addCases_left, Fin.addCases_right,
          Fin.val_castAdd, Fin.val_natAdd] at values
        omega
      · intro same
        have values := congrArg Fin.val same
        simp only [Fin.addCases_right, Fin.val_natAdd] at values
        have equal : first = second := Fin.ext (by omega)
        exact congrArg (Fin.natAdd 1) equal

/-- The declared controlled query is placed at its original stage and source positions. -/
@[expose]
public def queryApplication {phaseWidth : Nat} (systemWidth : Nat) (stage : Fin phaseWidth) :
    OracleModel.Application (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  OracleModel.Application.ofPositions (UnitarySource.model systemWidth true) (.controlled rfl)
    (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout
    (sourcePositions systemWidth stage) (fun _ => rfl)

/-- One actual explicitly granted controlled query at its stage control and source wires. -/
public def sourceQuery (gates : GateModel) {phaseWidth : Nat} (systemWidth : Nat) (stage : Fin
  phaseWidth) :
    UnitaryCircuit gates (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  .query (queryApplication systemWidth stage)

/-- Actual repeated source access realizes the binary stage multiplicity. -/
public def powerStage (gates : GateModel) {phaseWidth : Nat} (systemWidth : Nat) (stage : Fin
  phaseWidth) :
    UnitaryCircuit gates (UnitarySource.model systemWidth true)
      (QuantumSignature.qubits (phaseWidth + systemWidth)).canonicalPlacement.layout :=
  UnitaryCircuit.iterate (2 ^ stage.val) (sourceQuery gates systemWidth stage)

/-- The placed source query emits the granted controlled coordinate exactly once. -/
public lemma qpeNative_sourceQuery_eventCost (gates : GateModel)
    {phaseWidth : Nat} (systemWidth : Nat)
    (stage : Fin phaseWidth) :
    (sourceQuery gates systemWidth stage).eventCost =
      ResourcePool.singleton (model := .quantum gates (UnitarySource.model systemWidth true))
        (.oracle UnitarySource.Coordinate.controlled) := by
  rfl

/-- Stage multiplicities are counted from actual repetitions of the granted source query. -/
public lemma qpeNative_powerStage_eventCost (gates : GateModel)
    {phaseWidth : Nat} (systemWidth : Nat)
    (stage : Fin phaseWidth) :
    (powerStage gates systemWidth stage).eventCost = (2 ^ stage.val) •
      ResourcePool.singleton (model := .quantum gates (UnitarySource.model systemWidth true))
        (.oracle UnitarySource.Coordinate.controlled) := by
  rw [powerStage, UnitaryCircuit.iterate_eventCost, qpeNative_sourceQuery_eventCost]

end

end QuantumAlg.QuantumPhaseEstimation.Native
