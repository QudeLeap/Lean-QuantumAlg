/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.SemiclassicalFourier
public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.GateModel.SemiclassicalFourier
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Physical placement of measured Fourier gates

Both separately counted native instructions act on their one actual ambient
qubit. Their exact full-layout matrices equal the corresponding default-model
one-qubit instructions, including all spectators and global phase
[GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.SemiclassicalFourierGate

noncomputable section

variable {count : Nat} (layout : QuantumLayout count)

/-- Place the declared native one-qubit token at one real ambient position. -/
public def application (token : Token) (target : Fin count)
    (qubit : (layout.wire target).dimension = 2) : GateModel.Application model layout :=
  GateModel.Application.ofPositions model token layout
    ⟨fun _ => target, fun _ _ _ => Subsingleton.elim (α := Fin 1) _ _⟩
    (fun _ => qubit)

/-- Execute one separately counted native Hadamard at its actual physical wire. -/
public def hadamardAt (oracles : OracleModel) (target : Fin count)
    (qubit : (layout.wire target).dimension = 2) : UnitaryCircuit model oracles layout :=
  .native (application layout .hadamard target qubit)

/-- Execute one separately counted native single-qubit phase at its actual physical wire. -/
public def phaseAt (oracles : OracleModel) (angle : Real) (target : Fin count)
    (qubit : (layout.wire target).dimension = 2) : UnitaryCircuit model oracles layout :=
  .native (application layout (.phase angle) target qubit)

/-- Relabeling the Hadamard token leaves its entire ambient operator exactly unchanged. -/
public lemma semiclassicalFourier_hadamardAt_matrix (oracles : OracleModel)
    (target : Fin count) (qubit : (layout.wire target).dimension = 2)
      (environment : oracles.Interpretation) :
    ((hadamardAt layout oracles target qubit).matrix environment) =
      ((Gate.singleQubitAt layout oracles Gate.HOp target qubit).matrix environment) := by
  rfl

/-- Relabeling the phase token leaves its complete parameterized operator exactly unchanged. -/
public lemma semiclassicalFourier_phaseAt_matrix (oracles : OracleModel) (angle : Real)
    (target : Fin count) (qubit : (layout.wire target).dimension = 2)
      (environment : oracles.Interpretation) :
    ((phaseAt layout oracles angle target qubit).matrix environment) =
      ((Gate.singleQubitAt layout oracles (phaseGateOp angle) target qubit).matrix environment) :=
        by
  rfl

/-- One native Hadamard contributes exactly its own separately counted coordinate. -/
@[simp] public lemma semiclassicalFourier_hadamardAt_eventCost (oracles : OracleModel)
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    (hadamardAt layout oracles target qubit).eventCost =
      ResourcePool.singleton (model := .quantum model oracles) (.gate .hadamard) := by
  rfl

/-- One native phase contributes exactly its own separately counted coordinate. -/
@[simp] public lemma semiclassicalFourier_phaseAt_eventCost (oracles : OracleModel)
    (angle : Real) (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    (phaseAt layout oracles angle target qubit).eventCost =
      ResourcePool.singleton (model := .quantum model oracles) (.gate .phase) := by
  rfl

end

end QuantumAlg.SemiclassicalFourierGate
