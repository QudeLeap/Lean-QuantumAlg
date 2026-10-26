/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Encoded basis action on exactly the same ordered physical wires

The proof transports the actual native matrix through the original wire
correspondence. Keeping the register and word width abstract prevents a
consumer from normalizing a concrete large basis merely to change types.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

open Execution

variable {gates : GateModel} {oracles : OracleModel}
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {physical : QubitLayout encoding.width} {count : Nat} (target : QuantumLayout count)
    (sameWires : physical.toQuantum.wires = target.wires)

/-- A proved native basis action retains its exact ket under the original full wire placement. -/
lemma equalWires_apply_encoded_ket_of_eq
    (program : UnitaryCircuit gates oracles physical.toQuantum)
    (environment : oracles.Interpretation) (initial final : Data)
    (actual : program.applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode initial))) =
        NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode final))) :
    ((unitaryOfEqualWires physical.toQuantum target sameWires program).matrix environment).applyVec
      (NormalizedVector.ket
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode initial)))).vec =
      (NormalizedVector.ket
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode final)))).vec := by
  have raw := congrArg NormalizedVector.vec actual
  change (program.matrix environment).applyVec
    (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode initial))).vec = _ at raw
  have transported := congrArg
    (HilbertVector.reindex (R := physical.toQuantum.register) (S := target.register)
      (basisOfEqualWires physical.toQuantum target sameWires)) raw
  rw [← UnitaryOperator.reindex_applyVec, HilbertVector.reindex_ket,
    HilbertVector.reindex_ket] at transported
  rw [unitaryOfEqualWires_matrix]
  exact transported

/-- Full encoded realization supplies every placed basis column without unfolding the program. -/
lemma Realizes.equalWires_apply_encoded_ket
    {program : UnitaryCircuit gates oracles physical.toQuantum}
    {environment : oracles.Interpretation} {step : Data → Data}
    (actual : Realizes encoding program environment step) (state : Data) :
    ((unitaryOfEqualWires physical.toQuantum target sameWires program).matrix environment).applyVec
      (NormalizedVector.ket
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode state)))).vec =
      (NormalizedVector.ket
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode (step state))))).vec :=
  equalWires_apply_encoded_ket_of_eq target sameWires program environment state (step state)
    (actual.apply_encoded_ket state)

end

end QuantumAlg.UnitaryCircuit
