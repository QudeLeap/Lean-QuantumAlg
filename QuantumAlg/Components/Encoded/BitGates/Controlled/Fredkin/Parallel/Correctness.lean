/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin.Parallel.Frame
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-! # Complete source semantics of the actual paired Fredkin schedule -/

namespace QuantumAlg.EncodedBit.FredkinParallel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma cnot_gate_comm (control target : EncodedBit encoding) (gate : GateSpec encoding)
    (controlOutside : GateSpec.bitDisjoint control gate)
    (targetOutside : GateSpec.bitDisjoint target gate) (state : Data) :
    cnotStep control target (gate.step state) = gate.step (cnotStep control target state) := by
  unfold cnotStep
  rw [GateSpec.step_get_of_bitDisjoint gate control controlOutside]
  split
  · exact (GateSpec.step_flip_comm_of_bitDisjoint gate target targetOutside state).symm
  · rfl

namespace Frame

private lemma secondCnot_firstCnot (frame : Frame encoding) (state : Data) :
    frame.secondCnot.step (frame.firstCnot.step state) =
      frame.firstCnot.step (frame.secondCnot.step state) := by
  apply cnot_gate_comm
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide)⟩
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide)⟩

private lemma secondCnot_firstToffoli (frame : Frame encoding) (state : Data) :
    frame.secondCnot.step (frame.firstToffoli.step state) =
      frame.firstToffoli.step (frame.secondCnot.step state) := by
  apply cnot_gate_comm
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide),
      frame.wire_ne (by decide)⟩
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide),
      frame.wire_ne (by decide)⟩

private lemma firstCnot_secondToffoli (frame : Frame encoding) (state : Data) :
    frame.firstCnot.step (frame.secondToffoli.step state) =
      frame.secondToffoli.step (frame.firstCnot.step state) := by
  apply cnot_gate_comm
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide),
      frame.wire_ne (by decide)⟩
  · exact ⟨frame.wire_ne (by decide), frame.wire_ne (by decide),
      frame.wire_ne (by decide)⟩

/-- Reordering only genuinely disjoint payload operations preserves the entire state. -/
lemma scheduledGates_step (frame : Frame encoding) (state : Data) :
    GateSpec.stepList frame.scheduledGates state = GateSpec.stepList frame.serialGates state := by
  change frame.secondCnot.step (frame.firstCnot.step
    (frame.secondToffoli.step (frame.firstToffoli.step
      (frame.secondCnot.step (frame.firstCnot.step state))))) =
    frame.secondCnot.step (frame.secondToffoli.step
      (frame.secondCnot.step (frame.firstCnot.step
        (frame.firstToffoli.step (frame.firstCnot.step state)))))
  symm
  rw [secondCnot_firstCnot, secondCnot_firstToffoli, ← firstCnot_secondToffoli]

/-- Every original label, dirty payload, complement field and relative phase is retained. -/
lemma program_realizes (frame : Frame encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles) environment
      (GateSpec.stepList frame.serialGates) := by
  have actual := (frame.cnotLayer.program_realizes physical oracles environment).seq
    ((frame.firstToffoli.realizes physical oracles environment).seq
      ((frame.secondToffoli.realizes physical oracles environment).seq
        (frame.cnotLayer.program_realizes physical oracles environment)))
  apply actual.congrStep
  intro state
  exact frame.scheduledGates_step state

end Frame

end

end QuantumAlg.EncodedBit.FredkinParallel
