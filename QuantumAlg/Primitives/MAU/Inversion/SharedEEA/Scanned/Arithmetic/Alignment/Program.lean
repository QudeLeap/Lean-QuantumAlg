/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Barrel

/-! # Complete native barrel program, unchanged complement, and its paid resource coordinates -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Compile every original metadata-controlled Fredkin on the unchanged complete physical frame. -/
def program (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width first field)

/-- Every complete finite basis label and every coherent reference family is retained. -/
lemma program_realizes (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width first field) environment
      (GateSpec.stepList (gates width first field)) :=
  GateSpec.realizesList (QubitLayout.canonical _) .empty _ environment

/-- All actual bits outside the selected work word keep their arbitrary original values. -/
lemma gates_get_outside (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (observed : EncodedBit (encoding width))
    (outside : ∀ index, (ArithmeticRotation.bit width first index).wire ≠ observed.wire)
    (state : Data width) :
    observed.get (GateSpec.stepList (gates width first field) state) = observed.get state :=
  (barrel width first field).gates_get_outside (permutation width)
    (PermutationBarrel.binaryStages width.size) observed outside state

private lemma metadata_outside (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field)
    (index : Fin width.size) (wordIndex : Fin (width + 3)) :
    (ArithmeticRotation.bit width first wordIndex).wire ≠
      (ArithmeticGeometry.fieldBit width field index).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, ArithmeticGeometry.fieldBit_wire] at values
  have within := wordIndex.isLt
  cases first <;>
    simp only [Bool.false_eq_true, if_false, if_true] at values <;> omega

/-- Every original finite metadata field survives the real alignment, not only its control bits. -/
lemma gates_fieldValue (width : Nat) (first : Bool) (field observed : ArithmeticGeometry.Field)
    (state : Data width) :
    ArithmeticGeometry.fieldValue observed (GateSpec.stepList (gates width first field) state) =
      ArithmeticGeometry.fieldValue observed state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := gates_get_outside width first field
    (ArithmeticGeometry.fieldBit width observed ⟨index, within⟩)
    (fun wordIndex => metadata_outside width first observed ⟨index, within⟩ wordIndex) state
  simpa only [ArithmeticGeometry.fieldBit_get] using actual

/-- Both actual native counts and duration include all original full-metadata control stages. -/
lemma program_resources (width : Nat) (first : Bool) (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program width first field).eventCost ≤ (width + 3) * width.size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width first field).eventCost ≤ 2 * (width + 3) * width.size ∧
      (program width first field).evaluatedEventDepth Resource.Event.quantumDuration
        ≤ 3 * (width + 3) * width.size :=
  (barrel width first field).binary_resources (permutation width) (QubitLayout.canonical _) .empty

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
