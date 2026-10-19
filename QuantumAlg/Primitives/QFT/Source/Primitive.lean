/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Fourier
import all QuantumAlg.Components.GateModel.Fourier
public import QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Components.Gates.ControlledPhase.Physical
import all QuantumAlg.Components.Gates.ControlledPhase.QubitRegister
import all QuantumAlg.Components.Gates.Swap.Physical
import all QuantumAlg.Components.Gates.Swap.QubitRegister

/-!
# Addressed native Fourier instructions

Every source instruction selects its actual physical wires. The matrix laws
identify the full addressed operators, including every spectator coordinate.
-/

namespace QuantumAlg.QFTPrimitive
noncomputable section

private def positions {n : Nat} (first second : Fin n) (distinct : first ≠ second) :
    Fin 2 ↪ Fin n where
  toFun := ![first, second]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

/-- One actual native source instruction on the declared pair of qubits. -/
public def sourceCircuit {n : Nat} (primitive : QFTPrimitive n) (oracles : OracleModel) :
    UnitaryCircuit FourierGate.model oracles (layout n) :=
  match primitive with
  | .controlledPhase control target angle distinct =>
      .native (GateModel.Application.ofPositions FourierGate.model (.controlledPhase angle)
        (layout n) (positions control target distinct) (fun _ => rfl))
  | .swap left right distinct =>
      .native (GateModel.Application.ofPositions FourierGate.model .swap
        (layout n) (positions left right distinct) (fun _ => rfl))

/-- The primitive source gate has exactly the original addressed QFT operator. -/
public lemma qftPrimitive_sourceCircuit_matrix (oracles : OracleModel) {n : Nat}
    (primitive : QFTPrimitive n)
    (environment : oracles.Interpretation) :
    ((primitive.sourceCircuit oracles).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm primitive.operator := by
  cases primitive with
  | controlledPhase control target angle distinct =>
      rw [sourceCircuit, UnitaryCircuit.native_matrix,
        ← UnitaryCircuit.nativeApplication_operatorAt]
      exact (Gate.ControlledPhase.controlledPhase_circuitAt_matrix (environment := environment)
        (layout n) control target distinct rfl rfl oracles angle).symm.trans
          (Gate.ControlledPhase.controlledPhase_qubitCircuit_matrix (environment := environment)
            oracles control target distinct angle)
  | swap left right distinct =>
      rw [sourceCircuit, UnitaryCircuit.native_matrix,
        ← UnitaryCircuit.nativeApplication_operatorAt]
      exact (Gate.Swap.swap_circuitAt_matrix (environment := environment)
        (layout n) left right distinct rfl rfl oracles).symm.trans
          (Gate.Swap.swap_qubitCircuit_matrix (environment := environment) left right distinct
            oracles)

end
end QuantumAlg.QFTPrimitive
