/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Inversion.MK.Readout.Trace
import all QuantumAlg.Primitives.MAU.Inversion.MK.Physical.Circuit

/-!
# Encoded base-gate modular-inversion witnesses

This module provides reusable encoded witness interfaces for gate-structured
modular inversion and for lifting fixed-round Montgomery--Kaliski workspaces
[RNSL17, ECDLP.tex:390-465,753-755].  A concrete witness must supply a binary
label encoding and an actual `UnitaryCircuit` whose normalized basis action implements
its stated update; correctness and resource accounting then project from that
same object.  The static data-driven Montgomery correction and closing program
is defined separately in the `MK.Correction` and `MK.Resource` modules.
-/

section

namespace QuantumAlg
namespace MAU.Inversion

noncomputable section

/-- Raw-vector companion of a normalized actual-circuit realization.  Kept
private so the public witness surface remains normalization-preserving. -/
private theorem applyVec_encoded_ket_of_realizes {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    {program : UnitaryCircuit (Qubits encoding.width)} {step : Data -> Data}
    (h : UnitaryCircuit.Realizes encoding program step) (x : Data) :
    UnitaryCircuit.applyVec program
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode x) :
          HilbertVector (Qubits encoding.width)) =
      (NormalizedVector.ket (R := Qubits encoding.width)
        (encoding.encode (step x)) : HilbertVector (Qubits encoding.width)) := by
  simpa only [UnitaryCircuit.applyNormalized_coe] using
    congrArg
      (fun ψ : NormalizedVector (Qubits encoding.width) =>
        (ψ : HilbertVector (Qubits encoding.width)))
      (h.apply_encoded_ket x)

namespace StageState

/-- Reversible compute stage: add the modular inverse into the scratch register
rather than overwriting scratch. -/
def addInverseToScratch {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch + inverseResidue s.input
  flag := s.flag

/-- Inverse of the reversible compute stage. -/
def subInverseFromScratch {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch - inverseResidue s.input
  flag := s.flag

@[simp] theorem addInverseToScratch_subInverseFromScratch {N : Nat}
    (s : StageState N) :
    addInverseToScratch (subInverseFromScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

@[simp] theorem subInverseFromScratch_addInverseToScratch {N : Nat}
    (s : StageState N) :
    subInverseFromScratch (addInverseToScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

/-- Reversible compute/add/uncompute stage update for modular inversion,
following the fixed-round inversion route used for elliptic-curve resources
[RNSL17, ECDLP.tex:390-465]. -/
def reversibleScheduleStep {N : Nat} (s : StageState N) : StageState N :=
  subInverseFromScratch (addScratchToTarget (addInverseToScratch s))

/-- The reversible staged update agrees with the public clean inversion action
on clean scratch input. -/
theorem reversibleScheduleStep_initial {N : Nat}
    (u : (ZMod N)ˣ) (z : ZMod N) :
    reversibleScheduleStep (initial u z) =
      { input := u
        target := z + inverseResidue u
        inverseScratch := 0
        flag := false } := by
  simp [reversibleScheduleStep, initial, addInverseToScratch,
    addScratchToTarget, subInverseFromScratch]

/-- Product-tuple view used before relabeling a staged target-add witness back
to `StageState`. -/
abbrev FieldTuple (N : Nat) :=
  (ZMod N)ˣ × MAU.Addition.TargetAdd.Data N

/-- Tuple-level target-add action: add inverse scratch into the target field. -/
def tupleAddScratchToTarget {N : Nat} : FieldTuple N -> FieldTuple N
  | (input, fields) => (input, MAU.Addition.TargetAdd.step fields)

@[simp] theorem tupleAddScratchToTarget_toStage {N : Nat}
    (s : StageState N) :
    (tupleEquiv N).symm (tupleAddScratchToTarget (tupleEquiv N s)) =
      addScratchToTarget s := by
  cases s
  rfl

/-- A tuple-level target-add program over the explicit product field layout. -/
structure TupleTargetAddWitness {N n : Nat}
    (E : BinaryResidueEncoding N n) where
  /-- Program acting on the field tuple layout. -/
  program : UnitaryCircuit (Qubits (fieldTupleEncoding E).width)
  /-- Correctness of the target-add program on tuple labels. -/
  realizes :
    UnitaryCircuit.Realizes (fieldTupleEncoding E) program
      tupleAddScratchToTarget

namespace TupleTargetAddWitness

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- The relabeled target-add program realizes `StageState.addScratchToTarget`
on the staged-state field encoding. -/
theorem stage_realizes (w : TupleTargetAddWitness E) :
    UnitaryCircuit.Realizes (fieldEncoding E) w.program addScratchToTarget :=
  (w.realizes.relabel (tupleEquiv N)).congrStep
    tupleAddScratchToTarget_toStage

/-- Embed a modular-add target-update witness into the inversion field-tuple
layout by preserving the unit-input field. -/
def ofModularAddition (w : MAU.Addition.TargetAdd.Witness E) :
    TupleTargetAddWitness E where
  program := UnitaryCircuit.prodRight
    (m := (BinaryLabelEncoding.ofUnitResidueEncoding E).width) w.program
  realizes := UnitaryCircuit.Realizes.prodRight
    (left := BinaryLabelEncoding.ofUnitResidueEncoding E) w.realizes

end TupleTargetAddWitness

/-! ## Power-of-two clean-work target-add bridge -/

namespace PowerOfTwoTargetAdd

/-- Carry-work labels for the VBE target-add bridge used inside the staged
inversion layout [VBE95, 9511018.tex:237-264,591-618]. -/
abbrev CarryWork (n : Nat) : Type :=
  MAU.Addition.TargetAdd.PowerOfTwo.CarryWork n

/-- Distinguished clean carry-work label for the power-of-two target-add
bridge. -/
def cleanWork (n : Nat) : CarryWork n :=
  (MAU.Addition.TargetAdd.PowerOfTwo.cleanWorkWitness n).cleanWork

/-- Inverse-scratch bit lens for the power-of-two staged inversion encoding. -/
def inverseScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit
      (fieldEncoding
        (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n)) :=
  let E := MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n
  (BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit
        (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool
        (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)))).relabel
    (tupleEquiv (2 ^ n))

/-- Little-endian value bit lens for the staged inverse-scratch register. -/
def inverseScratchValueBit (n : Nat) (bit : Fin n) :
    EncodedBit
      (fieldEncoding
        (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n)) :=
  inverseScratchBit n bit

@[simp] theorem inverseScratchValueBit_get
    (n : Nat) (bit : Fin n) (s : StageState (2 ^ n)) :
    (inverseScratchValueBit n bit).get s =
      s.inverseScratch.val.testBit bit.val := by
  cases s with
  | mk input target inverseScratch flag =>
      change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get
          inverseScratch = inverseScratch.val.testBit bit.val
      exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit inverseScratch

/-- Field tuple plus target-add carry work.  The physical wire order is
input/target/inverse-scratch/flag/work, matching the staged inversion fields
followed by the VBE carry-work register [RNSL17, ECDLP.tex:390-465]. -/
abbrev FieldTupleWithWork (n : Nat) : Type :=
  FieldTuple (2 ^ n) × CarryWork n

/-- Product reassociation between the staged inversion field tuple with a
trailing work register and the product shape required by `prodRight`. -/
def fieldTupleWithWorkEquiv (n : Nat) :
    FieldTupleWithWork n ≃
      ((ZMod (2 ^ n))ˣ ×
        (MAU.Addition.TargetAdd.Data (2 ^ n) × CarryWork n)) where
  toFun := fun x => (x.1.1, (x.1.2, x.2))
  invFun := fun x => ((x.1, x.2.1), x.2.2)
  left_inv := by
    intro x
    rcases x with ⟨⟨input, fields⟩, work⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨input, rest⟩
    rcases rest with ⟨fields, work⟩
    rfl

/-- Tuple-level target-add with explicit carry work.  This is the same
wire-addressed VBE target-add circuit lifted under the preserved unit-input
field [VBE95, 9511018.tex:237-264,591-618]. -/
def tupleAddScratchToTargetWithWork (n : Nat) :
    FieldTupleWithWork n -> FieldTupleWithWork n
  | ((input, fields), work) =>
      let y :=
        (MAU.Addition.TargetAdd.PowerOfTwo.cleanWorkWitness n).stepWithWork
          (fields, work)
      ((input, y.1), y.2)

/-- Encoding of the tuple-level target-add layout with explicit carry work. -/
def tupleWithWorkEncoding (n : Nat) :
    BinaryLabelEncoding (FieldTupleWithWork n) :=
  (BinaryLabelEncoding.prod
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n))
    (MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkEncoding n)).relabel
      (fieldTupleWithWorkEquiv n)

/-- Actual tuple-level target-add circuit with explicit carry work. -/
def tupleWithWorkProgram (n : Nat) :
    UnitaryCircuit (Qubits (tupleWithWorkEncoding n).width) :=
  UnitaryCircuit.prodRight
    (m := (BinaryLabelEncoding.ofUnitResidueEncoding
      (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n)).width)
    (MAU.Addition.TargetAdd.PowerOfTwo.cleanWorkWitness n).program

/-- The lifted actual circuit realizes tuple-level target-add with work. -/
theorem tupleWithWork_realizes (n : Nat) :
    UnitaryCircuit.Realizes (tupleWithWorkEncoding n) (tupleWithWorkProgram n)
      (tupleAddScratchToTargetWithWork n) := by
  have h := UnitaryCircuit.Realizes.prodRight
    (left := BinaryLabelEncoding.ofUnitResidueEncoding
      (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n))
    (MAU.Addition.TargetAdd.PowerOfTwo.cleanWorkWitness n).realizes
  exact (h.relabel (fieldTupleWithWorkEquiv n)).congrStep (by
    intro x
    rcases x with ⟨⟨input, fields⟩, work⟩
    rfl)

/-- Clean tuple endpoint: on a clean flag and clean carry work, the work-aware
bridge agrees with the old tuple target-add action and restores work. -/
theorem tupleAddScratchToTargetWithWork_cleanEndpoint
    (n : Nat) (x : FieldTuple (2 ^ n)) (hflag : x.2.2.2 = false) :
    tupleAddScratchToTargetWithWork n (x, cleanWork n) =
      (tupleAddScratchToTarget x, cleanWork n) := by
  rcases x with ⟨input, fields⟩
  have h :=
    (MAU.Addition.TargetAdd.PowerOfTwo.cleanWorkWitness n).cleanEndpoint
      fields hflag
  simpa [tupleAddScratchToTargetWithWork, tupleAddScratchToTarget, cleanWork]
    using congrArg (fun y => ((input, y.1), y.2)) h

/-- Staged inversion state plus carry work. -/
abbrev StageWithWork (n : Nat) : Type :=
  StageState (2 ^ n) × CarryWork n

/-- Relabel staged records to the tuple-with-work layout used by the lifted
target-add circuit. -/
def stageWithWorkEquiv (n : Nat) :
    StageWithWork n ≃ FieldTupleWithWork n where
  toFun := fun x => ((tupleEquiv (2 ^ n)) x.1, x.2)
  invFun := fun x => ((tupleEquiv (2 ^ n)).symm x.1, x.2)
  left_inv := by
    intro x
    rcases x with ⟨s, work⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨fields, work⟩
    simp

/-- Work-aware staged target-add step.  This is only the target-add leg of the
RNSL fixed-round compute/add/uncompute route, with VBE carry work made explicit
[RNSL17, ECDLP.tex:390-465; VBE95, 9511018.tex:237-264,591-618]. -/
def addScratchToTargetWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) =>
      let y :=
        tupleAddScratchToTargetWithWork n ((tupleEquiv (2 ^ n)) s, work)
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)

/-- Encoding of staged inversion state plus explicit carry work. -/
def stageWithWorkEncoding (n : Nat) :
    BinaryLabelEncoding (StageWithWork n) :=
  (tupleWithWorkEncoding n).relabel (stageWithWorkEquiv n)

/-- Actual staged target-add circuit with explicit carry work. -/
def stageWithWorkProgram (n : Nat) :
    UnitaryCircuit (Qubits (stageWithWorkEncoding n).width) :=
  tupleWithWorkProgram n

/-- The actual staged circuit realizes the work-aware target-add step. -/
theorem stageWithWork_realizes (n : Nat) :
    UnitaryCircuit.Realizes (stageWithWorkEncoding n) (stageWithWorkProgram n)
      (addScratchToTargetWithWork n) :=
  ((tupleWithWork_realizes n).relabel (stageWithWorkEquiv n)).congrStep (by
    intro x
    rcases x with ⟨s, work⟩
    rfl)

/-- Inverse-scratch bit lens in the staged-state-plus-carry-work encoding. -/
def stageWithWorkInverseScratchValueBit (n : Nat) (bit : Fin n) :
    EncodedBit (stageWithWorkEncoding n) :=
  ((BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n))
    (MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkEncoding n)
    (MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit n bit)
    ).relabel (fieldTupleWithWorkEquiv n)).relabel
      (stageWithWorkEquiv n)

/-- Target bit in the staged-state-plus-carry-work encoding. -/
def stageWithWorkTargetValueBit (n : Nat) (bit : Fin n) :
    EncodedBit (stageWithWorkEncoding n) :=
  ((BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (MAU.Addition.TargetAdd.PowerOfTwo.residueEncoding n))
    (MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkEncoding n)
    (MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit n bit)
    ).relabel (fieldTupleWithWorkEquiv n)).relabel
      (stageWithWorkEquiv n)

@[simp] theorem stageWithWorkInverseScratchValueBit_wire_val
    (n : Nat) (bit : Fin n) :
    (stageWithWorkInverseScratchValueBit n bit).wire.val =
      n + (n + (n - 1 - bit.val)) := by
  simp [stageWithWorkInverseScratchValueBit,
    MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkScratchBit,
    MAU.Addition.TargetAdd.PowerOfTwo.scratchBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.ofUnitResidueEncoding,
    WireAddress.bitIndex, WireAddress.littleEndianWire,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]

@[simp] theorem stageWithWorkTargetValueBit_wire_val
    (n : Nat) (bit : Fin n) :
    (stageWithWorkTargetValueBit n bit).wire.val =
      n + (n - 1 - bit.val) := by
  simp [stageWithWorkTargetValueBit,
    MAU.Addition.TargetAdd.PowerOfTwo.withCarryWorkTargetBit,
    MAU.Addition.TargetAdd.PowerOfTwo.targetBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    BinaryLabelEncoding.ofUnitResidueEncoding,
    WireAddress.bitIndex, WireAddress.littleEndianWire,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire]

/-- Clean staged endpoint for the work-aware target-add leg. -/
theorem addScratchToTargetWithWork_cleanEndpoint
    (n : Nat) (s : StageState (2 ^ n)) (hflag : s.flag = false) :
    addScratchToTargetWithWork n (s, cleanWork n) =
      (addScratchToTarget s, cleanWork n) := by
  have htupleFlag :
      ((tupleEquiv (2 ^ n)) s).2.2.2 = false := by
    cases s
    simpa [tupleEquiv] using hflag
  have htuple :=
    tupleAddScratchToTargetWithWork_cleanEndpoint n
      ((tupleEquiv (2 ^ n)) s) htupleFlag
  change
    (let y :=
      tupleAddScratchToTargetWithWork n
        ((tupleEquiv (2 ^ n)) s, cleanWork n);
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)) =
      (addScratchToTarget s, cleanWork n)
  rw [htuple]
  simp [tupleAddScratchToTarget_toStage]

/-- Compute the inverse scratch while preserving the target-add carry work. -/
def addInverseToScratchWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) => (addInverseToScratch s, work)

/-- Reverse the inverse-scratch computation while preserving carry work. -/
def subInverseFromScratchWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n
  | (s, work) => (subInverseFromScratch s, work)

@[simp] theorem addInverseToScratchWithWork_subInverseFromScratchWithWork
    (n : Nat) (x : StageWithWork n) :
    addInverseToScratchWithWork n (subInverseFromScratchWithWork n x) = x := by
  rcases x with ⟨s, work⟩
  simp [addInverseToScratchWithWork, subInverseFromScratchWithWork]

/-- Work-aware reversible inversion schedule:
compute inverse scratch, add scratch into the target through the explicit VBE
carry-work bridge, then uncompute inverse scratch [RNSL17,
ECDLP.tex:390-465,753-755; VBE95, 9511018.tex:237-264,591-618]. -/
def reversibleScheduleStepWithWork (n : Nat) :
    StageWithWork n -> StageWithWork n :=
  fun x =>
    subInverseFromScratchWithWork n
      (addScratchToTargetWithWork n
        (addInverseToScratchWithWork n x))

/-- The work-aware decomposed schedule agrees with the clean public inversion
action when scratch, flag, and carry work start clean. -/
theorem reversibleScheduleStepWithWork_initial
    (n : Nat) (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n)) :
    reversibleScheduleStepWithWork n (initial u z, cleanWork n) =
      (({ input := u
          target := z + inverseResidue u
          inverseScratch := 0
          flag := false } : StageState (2 ^ n)),
        cleanWork n) := by
  unfold reversibleScheduleStepWithWork addInverseToScratchWithWork
    subInverseFromScratchWithWork
  rw [addScratchToTargetWithWork_cleanEndpoint n
    (addInverseToScratch (initial u z))]
  · simp [initial, addInverseToScratch, addScratchToTarget,
      subInverseFromScratch]
  · simp [initial, addInverseToScratch]

/-- Decomposed staged inversion witness with explicit VBE target-add carry work.
The target-add leg is fixed to `stageWithWorkProgram`; a closing proof must
still provide the inverse-scratch compute program under the same stage/work
encoding and prove that it realizes `addInverseToScratchWithWork`.  Concrete
fixed-round schedules and their history/workspace proofs are supplied by the
corresponding path/control witness rather than assumed by this generic
contract [RNSL17, ECDLP.tex:390-465,753-755]. -/
structure DecomposedStageWithTargetAddWitness (n : Nat) where
  /-- Program adding the inverse residue into scratch, in the same work-aware
  stage encoding used by the target-add bridge. -/
  computeProgram :
    UnitaryCircuit (Qubits (stageWithWorkEncoding n).width)
  /-- Correctness of the compute program on stage/work labels. -/
  computeRealizes :
    UnitaryCircuit.Realizes (stageWithWorkEncoding n)
      computeProgram (addInverseToScratchWithWork n)

namespace DecomposedStageWithTargetAddWitness

/-- Compute, work-aware target-add, and reverse-compute as one base-gate
program. -/
def program {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    UnitaryCircuit (Qubits (stageWithWorkEncoding n).width) :=
  UnitaryCircuit.seq w.computeProgram
    (UnitaryCircuit.seq (stageWithWorkProgram n) w.computeProgram.dagger)

/-- The decomposed work-aware program realizes the reversible inversion
schedule with explicit carry work. -/
theorem realizes {n : Nat} (w : DecomposedStageWithTargetAddWitness n) :
    UnitaryCircuit.Realizes (stageWithWorkEncoding n) w.program
      (reversibleScheduleStepWithWork n) := by
  have huncompute :
      UnitaryCircuit.Realizes (stageWithWorkEncoding n)
        w.computeProgram.dagger
        (subInverseFromScratchWithWork n) :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse w.computeRealizes
      (addInverseToScratchWithWork_subInverseFromScratchWithWork n)
  have htail :
      UnitaryCircuit.Realizes (stageWithWorkEncoding n)
        (UnitaryCircuit.seq (stageWithWorkProgram n) w.computeProgram.dagger)
        (fun x : StageWithWork n =>
          subInverseFromScratchWithWork n
            (addScratchToTargetWithWork n x)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := addScratchToTargetWithWork n)
      (secondStep := subInverseFromScratchWithWork n)
      (stageWithWork_realizes n) huncompute
  have hfull :
      UnitaryCircuit.Realizes (stageWithWorkEncoding n) w.program
        (reversibleScheduleStepWithWork n) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := addInverseToScratchWithWork n)
      (secondStep := fun x : StageWithWork n =>
        subInverseFromScratchWithWork n
          (addScratchToTargetWithWork n x))
      w.computeRealizes htail
  simpa [program, reversibleScheduleStepWithWork] using hfull

/-- Encoded-basis correctness for all work-aware staged inversion labels. -/
theorem apply_ket {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n) (x : StageWithWork n) :
    UnitaryCircuit.applyVec w.program
        (NormalizedVector.ket
          (R := Qubits (stageWithWorkEncoding n).width)
          ((stageWithWorkEncoding n).encode x) :
          HilbertVector (Qubits (stageWithWorkEncoding n).width)) =
      (NormalizedVector.ket
        (R := Qubits (stageWithWorkEncoding n).width)
        ((stageWithWorkEncoding n).encode
          (reversibleScheduleStepWithWork n x)) :
        HilbertVector (Qubits (stageWithWorkEncoding n).width)) := by
  exact applyVec_encoded_ket_of_realizes w.realizes x

/-- Clean encoded-basis action for the work-aware decomposed staged inversion
wrapper. -/
theorem apply_clean_ket {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n)
    (u : (ZMod (2 ^ n))ˣ) (z : ZMod (2 ^ n)) :
    UnitaryCircuit.applyVec w.program
        (NormalizedVector.ket
          (R := Qubits (stageWithWorkEncoding n).width)
          ((stageWithWorkEncoding n).encode
            (initial u z, cleanWork n)) :
          HilbertVector (Qubits (stageWithWorkEncoding n).width)) =
      (NormalizedVector.ket
        (R := Qubits (stageWithWorkEncoding n).width)
        ((stageWithWorkEncoding n).encode
          (({ input := u
              target := z + inverseResidue u
              inverseScratch := 0
              flag := false } : StageState (2 ^ n)),
            cleanWork n)) :
        HilbertVector (Qubits (stageWithWorkEncoding n).width)) := by
  simpa [reversibleScheduleStepWithWork_initial] using
    applyVec_encoded_ket_of_realizes w.realizes
      (initial u z, cleanWork n)



/-- Linearizing this exact work-aware circuit's strict event depth recovers
its event pool. -/
theorem resourcesFromEventDepth_eq_eventCost {n : Nat}
    (w : DecomposedStageWithTargetAddWitness n) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program

end DecomposedStageWithTargetAddWitness

end PowerOfTwoTargetAdd

/- Finite two-bit integration smoke for the staged target-add bridge.  This
reuses the concrete `ZMod 4` Toffoli/CNOT/CNOT target-add program inside the
field-packed inversion stage layout; it is not the full inversion compute
program [RNSL17, ECDLP.tex:390-465]. -/
namespace Mod4TargetAdd

/-- Tuple-level staged target-add witness induced by the concrete `ZMod 4`
modular-addition target update. -/
def tupleWitness :
    TupleTargetAddWitness MAU.Addition.TargetAdd.Mod4.residueEncoding :=
  TupleTargetAddWitness.ofModularAddition
    MAU.Addition.TargetAdd.Mod4.witness

/-- The concrete `ZMod 4` target-add program realizes the staged target update
after relabeling through the inversion field tuple. -/
theorem realizes :
    UnitaryCircuit.Realizes
      (fieldEncoding MAU.Addition.TargetAdd.Mod4.residueEncoding)
      tupleWitness.program addScratchToTarget :=
  tupleWitness.stage_realizes

end Mod4TargetAdd

end StageState

/-- Semantic update implemented by a decomposed gate-structured modular
inversion stage witness. -/
abbrev decomposedStageStep {N : Nat} : StageState N -> StageState N :=
  StageState.reversibleScheduleStep

/-- Decomposed gate-program witnesses for the reversible compute/add/uncompute
modular-inversion schedule.  The cleanup program is generated by reversing the
compute program, so compute and uncompute share one concrete gate sequence
[RNSL17, ECDLP.tex:390-465,753-755]. -/
structure DecomposedStageWitness (N : Nat) where
  /-- Faithful encoding of staged inversion labels, including scratch. -/
  encoding : BinaryLabelEncoding (StageState N)
  /-- Program adding the inverse residue into scratch. -/
  computeProgram : UnitaryCircuit (Qubits encoding.width)
  /-- Program adding scratch into the target accumulator. -/
  targetAddProgram : UnitaryCircuit (Qubits encoding.width)
  /-- Correctness of the compute program on encoded stage labels. -/
  computeRealizes :
    UnitaryCircuit.Realizes encoding computeProgram StageState.addInverseToScratch
  /-- Correctness of the target-add program on encoded stage labels. -/
  targetAddRealizes :
    UnitaryCircuit.Realizes encoding targetAddProgram StageState.addScratchToTarget

namespace DecomposedStageWitness

variable {N : Nat}

/-- Build a decomposed staged witness over the canonical field-packed
modular-inversion layout. -/
def ofFieldEncoding {N n : Nat} (E : BinaryResidueEncoding N n)
    (computeProgram targetAddProgram :
      UnitaryCircuit (Qubits (StageState.fieldEncoding E).width))
    (computeRealizes :
      UnitaryCircuit.Realizes (StageState.fieldEncoding E) computeProgram
        StageState.addInverseToScratch)
    (targetAddRealizes :
      UnitaryCircuit.Realizes (StageState.fieldEncoding E) targetAddProgram
        StageState.addScratchToTarget) :
    DecomposedStageWitness N where
  encoding := StageState.fieldEncoding E
  computeProgram := computeProgram
  targetAddProgram := targetAddProgram
  computeRealizes := computeRealizes
  targetAddRealizes := targetAddRealizes

@[simp] theorem ofFieldEncoding_encoding {N n : Nat}
    (E : BinaryResidueEncoding N n)
    (computeProgram targetAddProgram :
      UnitaryCircuit (Qubits (StageState.fieldEncoding E).width))
    (computeRealizes :
      UnitaryCircuit.Realizes (StageState.fieldEncoding E) computeProgram
        StageState.addInverseToScratch)
    (targetAddRealizes :
      UnitaryCircuit.Realizes (StageState.fieldEncoding E) targetAddProgram
        StageState.addScratchToTarget) :
    (ofFieldEncoding E computeProgram targetAddProgram computeRealizes
      targetAddRealizes).encoding = StageState.fieldEncoding E :=
  rfl

/-- Compute, target-add, and reverse-compute as one actual circuit. -/
def program (w : DecomposedStageWitness N) :
    UnitaryCircuit (Qubits w.encoding.width) :=
  UnitaryCircuit.seq w.computeProgram
    (UnitaryCircuit.seq w.targetAddProgram w.computeProgram.dagger)

/-- The decomposed program realizes the reversible inversion schedule. -/
theorem realizes (w : DecomposedStageWitness N) :
    UnitaryCircuit.Realizes w.encoding w.program
      (decomposedStageStep (N := N)) := by
  have huncompute :
      UnitaryCircuit.Realizes w.encoding w.computeProgram.dagger
        StageState.subInverseFromScratch :=
    UnitaryCircuit.Realizes.dagger_of_rightInverse w.computeRealizes
      StageState.addInverseToScratch_subInverseFromScratch
  have htail :
      UnitaryCircuit.Realizes w.encoding
        (UnitaryCircuit.seq w.targetAddProgram w.computeProgram.dagger)
        (fun x : StageState N =>
          StageState.subInverseFromScratch (StageState.addScratchToTarget x)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := StageState.addScratchToTarget)
      (secondStep := StageState.subInverseFromScratch)
      w.targetAddRealizes huncompute
  have hfull :
      UnitaryCircuit.Realizes w.encoding w.program
        (decomposedStageStep (N := N)) :=
    UnitaryCircuit.Realizes.seq
      (firstStep := StageState.addInverseToScratch)
      (secondStep := fun x : StageState N =>
        StageState.subInverseFromScratch (StageState.addScratchToTarget x))
      w.computeRealizes htail
  simpa [program, decomposedStageStep, StageState.reversibleScheduleStep] using hfull

/-- Encoded-basis correctness for all staged modular-inversion labels. -/
theorem apply_ket (w : DecomposedStageWitness N) (x : StageState N) :
    UnitaryCircuit.applyVec w.program
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          HilbertVector (Qubits w.encoding.width)) =
      (NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (StageState.reversibleScheduleStep x)) :
        HilbertVector (Qubits w.encoding.width)) :=
  applyVec_encoded_ket_of_realizes w.realizes x

/-- Clean staged action:
`|enc(u,z,0,0)> -> |enc(u,z+u^{-1},0,0)>`. -/
theorem apply_clean_ket (w : DecomposedStageWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    UnitaryCircuit.applyVec w.program
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (StageState.initial u z)) :
          HilbertVector (Qubits w.encoding.width)) =
      (NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u
             target := z + inverseResidue u
             inverseScratch := 0
             flag := false } : StageState N)) :
        HilbertVector (Qubits w.encoding.width)) := by
  simpa [StageState.reversibleScheduleStep_initial] using
    apply_ket w (StageState.initial u z)

/-- Intrinsically normalized correctness for every staged label of the exact
compute / target-add / inverse-compute circuit. -/
theorem applyNormalized_ket (w : DecomposedStageWitness N) (x : StageState N) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (StageState.reversibleScheduleStep x)) :=
  w.realizes.apply_encoded_ket x

/-- Normalized clean staged action of the exact decomposed inversion circuit. -/
theorem applyNormalized_clean_ket (w : DecomposedStageWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    w.program.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (StageState.initial u z))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u
             target := z + inverseResidue u
             inverseScratch := 0
             flag := false } : StageState N)) := by
  simpa [StageState.reversibleScheduleStep_initial] using
    applyNormalized_ket w (StageState.initial u z)

/-- Ordered strict event trace of the exact decomposed inversion circuit. -/
def eventTrace (w : DecomposedStageWitness N) :
    List (Resource.Event .quantum) :=
  w.program.eventTrace

/-- Strict event pool of the exact decomposed inversion circuit. -/
def eventCost (w : DecomposedStageWitness N) : ResourcePool .quantum :=
  w.program.eventCost

/-- Strict symbolic event critical path of the exact decomposed circuit. -/
def eventDepth (w : DecomposedStageWitness N) :
    DepthExpr (Resource.Event .quantum) :=
  w.program.eventDepth

/-- Evaluated event depth of the exact decomposed circuit. -/
def evaluatedEventDepth (w : DecomposedStageWitness N)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  w.program.evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the decomposed circuit. -/
def eventQueryDepth (w : DecomposedStageWitness N)
    (event : Resource.Event .quantum) : Nat :=
  w.program.eventQueryDepth event

/-- Exact multiplicity of one gate coordinate in the decomposed event pool. -/
def eventGateCount (w : DecomposedStageWitness N)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.program.eventCost













/-- Linearizing decomposed event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost (w : DecomposedStageWitness N) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program

end DecomposedStageWitness

/-- Semantic update implemented by a gate-structured modular-inversion witness. -/
abbrev encodedStep {N : Nat} : Data N -> Data N :=
  Data.addInverseIntoTarget

/-- Domain-specific modular-inversion witness tied directly to one actual
circuit and its encoded-basis realization. -/
structure StructuredCircuitWitness (N : Nat) where
  /-- Faithful encoding of modular-inversion labels. -/
  encoding : BinaryLabelEncoding (Data N)
  /-- Actual modular-inversion circuit. -/
  circuit : UnitaryCircuit (Qubits encoding.width)
  /-- Direct encoded-basis realization of the public inversion update. -/
  realizes : UnitaryCircuit.Realizes encoding circuit (encodedStep (N := N))

namespace StructuredCircuitWitness

variable {N : Nat}

/-- Encoded-basis correctness for all modular-inversion data labels. -/
theorem apply_ket (w : StructuredCircuitWitness N) (x : Data N) :
    UnitaryCircuit.applyVec w.circuit
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          HilbertVector (Qubits w.encoding.width)) =
      (NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addInverseIntoTarget) :
        HilbertVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using applyVec_encoded_ket_of_realizes w.realizes x

/-- Clean public-form encoded-basis action:
`|enc(u,z,0)> -> |enc(u,z+u^{-1},0)>`. -/
theorem apply_clean_ket (w : StructuredCircuitWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    UnitaryCircuit.applyVec w.circuit
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := u, target := z, flag := false } : Data N)) :
          HilbertVector (Qubits w.encoding.width)) =
      (NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u, target := z + inverseResidue u, flag := false } : Data N)) :
        HilbertVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addInverseIntoTarget] using
    apply_ket (N := N) w
      ({ input := u, target := z, flag := false } : Data N)

/-- Intrinsically normalized encoded-basis correctness. -/
theorem applyNormalized_ket (w : StructuredCircuitWitness N) (x : Data N) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width) (w.encoding.encode x)) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addInverseIntoTarget) := by
  simpa [encodedStep] using
    w.realizes.apply_encoded_ket x

/-- Normalized clean public-form action of the exact accounted circuit. -/
theorem applyNormalized_clean_ket (w : StructuredCircuitWitness N)
    (u : (ZMod N)ˣ) (z : ZMod N) :
    w.circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ input := u, target := z, flag := false } : Data N))) =
      NormalizedVector.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ input := u, target := z + inverseResidue u, flag := false } : Data N)) := by
  simpa [Data.addInverseIntoTarget] using
    applyNormalized_ket (N := N) w
      ({ input := u, target := z, flag := false } : Data N)

/-- Ordered strict event trace of the exact structured inversion circuit. -/
def eventTrace (w : StructuredCircuitWitness N) :
    List (Resource.Event .quantum) :=
  w.circuit.eventTrace

/-- Strict event pool of the exact structured inversion circuit. -/
def eventCost (w : StructuredCircuitWitness N) : ResourcePool .quantum :=
  w.circuit.eventCost

/-- Strict symbolic event critical path of the structured circuit. -/
def eventDepth (w : StructuredCircuitWitness N) :
    DepthExpr (Resource.Event .quantum) :=
  w.circuit.eventDepth

/-- Evaluated event depth of the exact structured circuit. -/
def evaluatedEventDepth (w : StructuredCircuitWitness N)
    (assign : Resource.Event .quantum → Nat) : Nat :=
  w.circuit.evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the structured circuit. -/
def eventQueryDepth (w : StructuredCircuitWitness N)
    (event : Resource.Event .quantum) : Nat :=
  w.circuit.eventQueryDepth event

/-- Exact multiplicity of one gate coordinate in the structured event pool. -/
def eventGateCount (w : StructuredCircuitWitness N)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) w.circuit.eventCost













/-- Linearizing structured event depth recovers its exact strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost (w : StructuredCircuitWitness N) :
    w.circuit.resourcesFromEventDepth = w.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.circuit

end StructuredCircuitWitness

end

end MAU.Inversion
end QuantumAlg

end
