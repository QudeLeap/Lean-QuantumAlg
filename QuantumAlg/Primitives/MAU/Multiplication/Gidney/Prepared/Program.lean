/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Core.Execution.Circuit

/-!
# Prepare and execute the unit multiplier on its actual live context

The circuit allocates its auxiliary zero word, executes the already proved
native multiplier on the same source/auxiliary physical identities, and
retains both live words. A zero-event identity records the complete existing
carrier in the context's ordered wire list. It allocates no new system and
changes no gate placement, quantum state, or event schedule.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

/-- Independent arithmetic action expressed in the complete actual physical context. -/
def preparedOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryOperator (preparedContext width).register :=
  UnitaryOperator.reindex (preparedWordBasisEquiv width).symm
    (wordUnitMultiplicationOperator width modulus coefficient)

/-- The placed actual multiplier with its complete existing physical carrier. -/
def preparedUnitary (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryCircuit (preparedContext width).register :=
  (UnitaryCircuit.reindex (R := Qubits (Accumulate.Gidney.encoding width).width)
    (preparedWordBasisEquiv width).symm
    (program width modulus coefficient)).seq
      (UnitaryCircuit.identity (preparedContext width).register
        (preparedContext width).physicalIdx (preparedContext width).identitiesNodup)

theorem gidneyPreparedUnitary_matrix (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).matrix =
      preparedOperator width modulus coefficient := by
  let transported : UnitaryCircuit (preparedContext width).register :=
    UnitaryCircuit.reindex (R := Qubits (Accumulate.Gidney.encoding width).width)
      (preparedWordBasisEquiv width).symm (program width modulus coefficient)
  let carrier := UnitaryCircuit.identity (preparedContext width).register
    (preparedContext width).physicalIdx (preparedContext width).identitiesNodup
  have transportedMatrix : transported.matrix = preparedOperator width modulus coefficient :=
    (UnitaryCircuit.reindex_matrix (R := Qubits (Accumulate.Gidney.encoding width).width)
      (S := (preparedContext width).register) (preparedWordBasisEquiv width).symm
      (program width modulus coefficient)).trans
        (congrArg (fun operator :
            UnitaryOperator (Qubits (Accumulate.Gidney.encoding width).width) =>
          UnitaryOperator.reindex (preparedWordBasisEquiv width).symm operator)
          (gidneyUnitMultiplication_matrix width modulus coefficient))
  apply Subtype.ext
  exact (UnitaryCircuit.seq_matrix transported carrier).trans
    ((congrArg₂ (fun left right : HilbertOperator (preparedContext width).register => left * right)
      (UnitaryCircuit.identity_matrix (preparedContext width).register
        (preparedContext width).physicalIdx (preparedContext width).identitiesNodup)
      (congrArg (fun operator : UnitaryOperator (preparedContext width).register =>
        (operator : HilbertOperator (preparedContext width).register)) transportedMatrix)).trans
          (one_mul _))

theorem gidneyPreparedUnitary_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).physical_idx =
      (preparedContext width).physicalIdx := by
  change (UnitaryCircuit.reindex (preparedWordBasisEquiv width).symm
    (program width modulus coefficient)).physical_idx ∪
      (preparedContext width).physicalIdx = (preparedContext width).physicalIdx
  apply List.Subset.union_eq_right
  change (program width modulus coefficient).physical_idx ⊆ (preparedContext width).physicalIdx
  rw [gidneyUnitMultiplication_physical]
  exact gidneyPreparedContext_contains width

theorem gidneyPreparedUnitary_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).eventCost =
      (program width modulus coefficient).eventCost := by
  change (program width modulus coefficient).eventCost + 0 =
    (program width modulus coefficient).eventCost
  exact add_zero _

theorem gidneyPreparedUnitary_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).evaluatedEventDepth (fun _ => 1) =
      (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) := by
  change (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) + 0 = _
  exact Nat.add_zero _

/-- The actual native execution prepares the missing word internally before the unitary. -/
def preparedCode (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    Circuit (Execution.OwnedQubits.context width) (preparedContext width) :=
  (Circuit.prepare (Execution.OwnedQubits.context width) auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
    (auxiliaryPreparation width)).seq
      (Circuit.unitary (preparedUnitary width modulus coefficient)
        (gidneyPreparedUnitary_physical width modulus coefficient))

end

end QuantumAlg.MAU.Multiplication.Gidney
