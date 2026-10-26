/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Native affine controls for the static measured adder

A static offset bit selects either zero or the quantum-control bit. Conjugating
an addressed Toffoli by the corresponding actual CNOTs realizes both affine
controls without an additional Toffoli. Every conjugated wire is restored,
including its coherences with arbitrary other encoded wires
[G25, main.tex:354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- One actual Toffoli with zero or the same quantum bit xored into each control. -/
def affineToffoliGates (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool) :
    List (GateSpec encoding) :=
  (if useFirst then [.cnot offset first offsetFirst] else []) ++
    (if useSecond then [.cnot offset second offsetSecond] else []) ++
      [.toffoli first second output firstSecond firstOutput secondOutput] ++
        (if useSecond then [.cnot offset second offsetSecond] else []) ++
          (if useFirst then [.cnot offset first offsetFirst] else [])

/-- All controls and other original bits are restored; only the selected output is xored. -/
lemma affineToffoliGates_step (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (offsetOutput : offset.wire ≠ output.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool) (state : Data) :
    stepList (affineToffoliGates offset first second output offsetFirst offsetSecond
      firstSecond firstOutput secondOutput useFirst useSecond) state =
      if (first.get state ^^ (useFirst && offset.get state)) &&
          (second.get state ^^ (useSecond && offset.get state)) then output.flip state
      else state := by
  have offsetAtFirst := EncodedBit.get_flip_of_wire_ne first offset offsetFirst.symm
  have offsetAtSecond := EncodedBit.get_flip_of_wire_ne second offset offsetSecond.symm
  have offsetAtOutput := EncodedBit.get_flip_of_wire_ne output offset offsetOutput.symm
  have firstAtSecond := EncodedBit.get_flip_of_wire_ne second first firstSecond.symm
  have secondAtFirst := EncodedBit.get_flip_of_wire_ne first second firstSecond
  cases useFirst <;> cases useSecond <;> cases offsetValue : offset.get state <;>
    cases firstValue : first.get state <;> cases secondValue : second.get state <;>
    simp [affineToffoliGates, stepList, step,
      EncodedBit.cnotStep, EncodedBit.toffoliStep, offsetAtFirst, offsetAtSecond,
      offsetAtOutput, firstAtSecond, secondAtFirst, EncodedBit.flip_comm first output,
      EncodedBit.flip_comm second output, EncodedBit.get_flip_self,
      EncodedBit.flip_flip, offsetValue, firstValue, secondValue]

/-- The same literal word charges one Toffoli and exactly its four possible conjugating CNOTs. -/
lemma affineToffoliGates_events (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool)
    (oracles : OracleModel) :
    (affineToffoliGates offset first second output offsetFirst offsetSecond firstSecond
      firstOutput secondOutput useFirst useSecond).map (event oracles) =
      List.replicate (useFirst.toNat + useSecond.toNat) (.gate .cnot) ++
        [.gate .toffoli] ++ List.replicate (useFirst.toNat + useSecond.toNat) (.gate .cnot) := by
  cases useFirst <;> cases useSecond <;> rfl

/-- A clean false second control makes the entire literal conjugated word an identity. -/
lemma affineToffoliGates_step_of_second_zero
    (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (offsetOutput : offset.wire ≠ output.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst : Bool) (state : Data)
    (clean : second.get state = false) :
    stepList (affineToffoliGates offset first second output offsetFirst offsetSecond
      firstSecond firstOutput secondOutput useFirst false) state = state := by
  rw [affineToffoliGates_step offset first second output offsetFirst offsetSecond
    offsetOutput firstSecond firstOutput secondOutput useFirst false state]
  simp [clean]

/-- Affine controls add actual CNOTs while retaining exactly one native Toffoli. -/
lemma affineToffoliGates_toffoliMultiplicity (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool) :
    ((affineToffoliGates offset first second output offsetFirst offsetSecond firstSecond
      firstOutput secondOutput useFirst useSecond).map toffoliMultiplicity).sum = 1 := by
  cases useFirst <;> cases useSecond <;> rfl

/-- The two actual conjugating CNOTs are charged for each enabled affine control. -/
lemma affineToffoliGates_cnotMultiplicity (offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool) :
    ((affineToffoliGates offset first second output offsetFirst offsetSecond firstSecond
      firstOutput secondOutput useFirst useSecond).map cnotMultiplicity).sum =
      2 * (useFirst.toNat + useSecond.toNat) := by
  cases useFirst <;> cases useSecond <;> rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured
