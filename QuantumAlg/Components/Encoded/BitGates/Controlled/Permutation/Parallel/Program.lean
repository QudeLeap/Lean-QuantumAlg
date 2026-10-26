/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Commutation

/-! # Actual paired-exchange execution of two complete native permutation words -/

namespace QuantumAlg.EncodedBit.PermutationParallel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- A complete encoding and exact basis action determine the entire physical operator. -/
lemma matrix_eq_of_realizes (onto : Function.Surjective encoding.encode)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (first second : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (step : Data → Data) (environment : oracles.Interpretation)
    (firstActual : UnitaryCircuit.Realizes encoding first environment step)
    (secondActual : UnitaryCircuit.Realizes encoding second environment step) :
    first.matrix environment = second.matrix environment := by
  apply Subtype.ext
  ext row column
  obtain ⟨input, encoded⟩ := onto (physical.basisEquiv column)
  have same := (firstActual.apply_encoded_ket input).trans
    (secondActual.apply_encoded_ket input).symm
  have entry := congrArg (fun state => state row) same
  change first.applyVec environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode input))).vec row =
    second.applyVec environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode input))).vec row at entry
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at entry
  simpa only [encoded, Equiv.symm_apply_apply] using entry

namespace Frame

/-- Every transposition executes two real CNOT layers and two serial common-control Toffolis. -/
def program (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    List (Permutation.Transposition (Fin size)) →
      UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model oracles physical.toQuantum
  | exchange :: rest => ((frame.exchangeFrame exchange).program physical oracles).seq
      (frame.program physical oracles rest)

/-- Source commutation preserves all retained metadata and every arbitrary payload amplitude. -/
lemma program_realizes (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Permutation.Transposition (Fin size)))
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles exchanges) environment
      (GateSpec.stepList (frame.serialGates exchanges)) := by
  induction exchanges with
  | nil => exact UnitaryCircuit.Realizes.identityAt _ _ encoding physical environment
  | cons exchange rest ih =>
      have head := (frame.exchangeFrame exchange).program_realizes physical oracles environment
      rw [exchangeFrame_serialGates] at head
      apply (head.seq ih).congrStep
      intro state
      have commute := frame.leftFrame.gates_comm frame.rightFrame rest [exchange]
        frame.cross frame.controlRight frame.controlLeft
        (GateSpec.stepList (frame.leftFrame.gates [exchange]) state)
      have actual := congrArg (GateSpec.stepList (frame.rightFrame.gates rest)) commute
      simpa only [serialGates, PermutationFrame.gates, GateSpec.stepList_append,
        GateSpec.stepList, id_eq] using actual

end Frame

end

end QuantumAlg.EncodedBit.PermutationParallel
