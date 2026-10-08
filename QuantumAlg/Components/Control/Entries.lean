/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.FinPow
public import QuantumAlg.Components.Control
import all QuantumAlg.Components.Control
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Exact entries of a qubit-controlled mathematical operator

The control value is preserved in both branches. These are mathematical
entries; executable controlled access is independently declared or realized.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

/-- A leading qubit control selects the source operator or the full target identity. -/
public theorem controlledQubits_pair_entry {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (rowControl columnControl : Fin 2)
    (rowSource columnSource : Fin (2 ^ width)) :
    controlledQubits unitary (prodEquiv (rowControl, rowSource))
      (prodEquiv (columnControl, columnSource)) =
        if rowControl = columnControl then
          if rowControl = 1 then unitary rowSource columnSource
          else if rowSource = columnSource then 1 else 0
        else 0 := by
  change controlled (Qubits 1) (1 : Fin 2) unitary
    ((prodEquiv (m := 1) (n := width)).symm (prodEquiv (rowControl, rowSource)))
    ((prodEquiv (m := 1) (n := width)).symm (prodEquiv (columnControl, columnSource))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, controlled_apply]

end

end QuantumAlg.UnitaryOperator
