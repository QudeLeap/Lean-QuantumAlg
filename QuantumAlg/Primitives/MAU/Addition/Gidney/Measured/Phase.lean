/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Branch

/-!
# Actual selected Z phase and cancellation of arbitrary dirty characters

The same stored outcome selects one native Z or identity. The original dirty
bit cancels between the phase pass before carry xor and the pass afterwards;
no basis-state or separability promise is made on that bit. The actual vent's
remaining carry character is then removed [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}

/-- The exact native selected phase equals the character retained by the physical vent. -/
lemma phaseProgram_applyVec_encoded_ket (physical : QubitLayout encoding.width)
    (target : EncodedBit encoding) (outcome : Fin 2) {environment : oracles.Interpretation}
    (state : Data) :
    (Instruction.phaseProgram (oracles := oracles) physical target outcome).applyVec environment
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      MeasuredUncompute.character outcome (target.get state) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  by_cases selected : outcome = 1
  · rw [Instruction.phaseProgram, if_pos selected, pauliZ_applyVec_encoded_ket]
    cases target.get state <;> simp [MeasuredUncompute.character, selected]
  · rw [Instruction.phaseProgram, if_neg selected, UnitaryCircuit.applyVec_identity]
    simp [MeasuredUncompute.character, selected]

/-- The actual selected phase has one native event exactly on outcome one. -/
lemma phaseProgram_eventTrace (physical : QubitLayout encoding.width)
    (target : EncodedBit encoding) (outcome : Fin 2) :
    (Instruction.phaseProgram (oracles := oracles) physical target outcome).eventTrace =
      if outcome = 1 then [.gate .singleQubit] else [] := by
  by_cases selected : outcome = 1 <;>
    simp [Instruction.phaseProgram, selected, pauliZ_eventTrace,
      UnitaryCircuit.identity_eventTrace]

/-- Both paid dirty phases retain only their carry character for every original dirty value. -/
lemma dirty_phase_cancel (outcome : Fin 2) (original carry : Bool) :
    MeasuredUncompute.character outcome (original ^^ carry) *
        MeasuredUncompute.character outcome original =
      MeasuredUncompute.character outcome carry := by
  by_cases selected : outcome = 1 <;> cases original <;> cases carry <;>
    norm_num [MeasuredUncompute.character, selected]

/-- The actual vent character cancels the two dirty phases, with exact scalar one. -/
lemma vented_phase_cancel (outcome : Fin 2) (original carry : Bool) :
    MeasuredUncompute.character outcome carry *
        MeasuredUncompute.character outcome (original ^^ carry) *
          MeasuredUncompute.character outcome original = 1 := by
  by_cases selected : outcome = 1 <;> cases original <;> cases carry <;>
    norm_num [MeasuredUncompute.character, selected]

end

end QuantumAlg.MAU.Addition.Gidney.Measured
