/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Core.Algorithm.Unitary.Owned
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual live space of complete owned qubit execution

Both peak ledgers are evaluated on the actual complete execution path. Every
supplied owned qubit remains live, and no classical workspace is introduced.
The equal-wire placement does not hide any additional systems.
-/

namespace QuantumAlg.UnitaryExecution.Owned.Binary
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {width : Nat}

private lemma layout_dimensionCount (dimension : ℕ+) :
    (layout width).dimensionCount dimension = if (2 : ℕ+) = dimension then width else 0 :=
  QuantumLayout.dimensionCount_uniform width 2 dimension Fin.val Fin.val_injective

/-- The actual resident peak counts precisely the physical qubits in the supplied interface. -/
public lemma ownedBinary_resident_systems (word : UnitaryCircuit gates oracles (layout width))
    (path : (algorithm word).run.code.Path) (dimension : ℕ+) :
    (algorithm word).run.code.peakResidentSpace path (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then width else 0 := by
  change Nat.max ((context (layout width)).residentSpace (.quantumSystems dimension)) 0 = _
  refine (Nat.max_zero _).trans ?_
  simp only [context, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_empty, add_zero]
  exact layout_dimensionCount dimension

/-- Every supplied owned qubit is included in the actual auxiliary peak. -/
public lemma ownedBinary_auxiliary_systems (word : UnitaryCircuit gates oracles (layout width))
    (path : (algorithm word).run.code.Path) (dimension : ℕ+) :
    (algorithm word).run.code.peakAuxiliarySpace path (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then width else 0 := by
  change Nat.max ((context (layout width)).auxiliarySpace (.quantumSystems dimension)) 0 = _
  refine (Nat.max_zero _).trans ?_
  simp only [context, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_empty, add_zero]
  exact layout_dimensionCount dimension

/-- The actual complete unitary execution introduces no classical bit storage. -/
public lemma ownedBinary_resident_classical (word : UnitaryCircuit gates oracles (layout width))
    (path : (algorithm word).run.code.Path) :
    (algorithm word).run.code.peakResidentSpace path .classicalBits = 0 := by
  rfl

/-- No hidden classical auxiliary storage is used by the unitary execution. -/
public lemma ownedBinary_auxiliary_classical (word : UnitaryCircuit gates oracles (layout width))
    (path : (algorithm word).run.code.Path) :
    (algorithm word).run.code.peakAuxiliarySpace path .classicalBits = 0 := by
  rfl

end
end QuantumAlg.UnitaryExecution.Owned.Binary
