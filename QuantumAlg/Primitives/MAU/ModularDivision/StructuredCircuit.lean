/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Colex
public import QuantumAlg.Core.Components.BaseGateRealization
public import QuantumAlg.Primitives.MAU.ModularAddition.StructuredCircuit
public import QuantumAlg.Primitives.MAU.ModularDivision.Layout
public import QuantumAlg.Primitives.MAU.ModularDivision.Pipeline

/-!
# Encoded base-gate modular-division witnesses

This module provides the MAU-facing wrapper for a future concrete
Toffoli/CNOT/X modular-division program following the inverse/multiply/add/
uncompute route selected from Proos--Zalka [PZ03, ecc.tex:622-640].  A closing
witness must supply a binary label encoding and a `BaseGateProgram` whose label
action implements the unit-denominator division update.  The folded `Circuit`
is then the same object used for encoded-basis correctness and resource
accounting.
-/

@[expose] public section

namespace QuantumAlg
namespace ModularDivision

noncomputable section

namespace PipelineState

/-- Reversible inverse-computation stage: add the denominator inverse into the
inverse scratch register rather than overwriting scratch. -/
def addInverseToScratch {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := s.inverseScratch +
    ModularInversion.inverseResidue s.denominator
  quotientScratch := s.quotientScratch
  flag := s.flag

/-- Inverse of the reversible inverse-computation stage. -/
def subInverseFromScratch {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := s.inverseScratch -
    ModularInversion.inverseResidue s.denominator
  quotientScratch := s.quotientScratch
  flag := s.flag

/-- Reversible quotient-computation stage: add `numerator * inverseScratch`
into quotient scratch. -/
def addProductToQuotientScratch {N : Nat}
    (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := s.inverseScratch
  quotientScratch := s.quotientScratch + s.numerator * s.inverseScratch
  flag := s.flag

/-- Inverse of the reversible quotient-computation stage. -/
def subProductFromQuotientScratch {N : Nat}
    (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := s.inverseScratch
  quotientScratch := s.quotientScratch - s.numerator * s.inverseScratch
  flag := s.flag

@[simp] theorem addInverseToScratch_subInverseFromScratch {N : Nat}
    (s : PipelineState N) :
    addInverseToScratch (subInverseFromScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

@[simp] theorem subInverseFromScratch_addInverseToScratch {N : Nat}
    (s : PipelineState N) :
    subInverseFromScratch (addInverseToScratch s) = s := by
  cases s
  simp [addInverseToScratch, subInverseFromScratch, sub_eq_add_neg, add_assoc]

@[simp] theorem addProductToQuotientScratch_subProductFromQuotientScratch
    {N : Nat} (s : PipelineState N) :
    addProductToQuotientScratch (subProductFromQuotientScratch s) = s := by
  cases s
  simp [addProductToQuotientScratch, subProductFromQuotientScratch,
    sub_eq_add_neg, add_assoc]

@[simp] theorem subProductFromQuotientScratch_addProductToQuotientScratch
    {N : Nat} (s : PipelineState N) :
    subProductFromQuotientScratch (addProductToQuotientScratch s) = s := by
  cases s
  simp [addProductToQuotientScratch, subProductFromQuotientScratch,
    sub_eq_add_neg, add_assoc]

/-- Reversible inverse/product/add/uncompute update for modular division,
following the Proos--Zalka unit-denominator division route
[PZ03, ecc.tex:622-640]. -/
def reversiblePipelineStep {N : Nat} (s : PipelineState N) : PipelineState N :=
  subInverseFromScratch
    (subProductFromQuotientScratch
      (addQuotientToTarget
        (addProductToQuotientScratch
          (addInverseToScratch s))))

/-- The reversible staged update agrees with the public clean division action
on clean scratch input. -/
theorem reversiblePipelineStep_initial {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    reversiblePipelineStep (initial u v z) =
      { denominator := u
        numerator := v
        target := z + quotientResidue u v
        inverseScratch := 0
        quotientScratch := 0
        flag := false } := by
  simp [reversiblePipelineStep, initial, addInverseToScratch,
    addProductToQuotientScratch, addQuotientToTarget,
    subProductFromQuotientScratch, subInverseFromScratch,
    quotientResidue]

/-- Product-tuple view used before relabeling a staged target-add witness back
to `PipelineState`. -/
abbrev FieldTuple (N : Nat) :=
  (ZMod N)ˣ × (ZMod N × ModularAddition.TargetAddWithAux.Data N)

/-- Tuple-level target-add action: add quotient scratch into the target field. -/
def tupleAddQuotientToTarget {N : Nat} : FieldTuple N -> FieldTuple N
  | (denominator, (numerator, fields)) =>
      (denominator, (numerator, ModularAddition.TargetAddWithAux.step fields))

@[simp] theorem tupleAddQuotientToTarget_toPipeline {N : Nat}
    (s : PipelineState N) :
    (tupleEquiv N).symm (tupleAddQuotientToTarget (tupleEquiv N s)) =
      addQuotientToTarget s := by
  cases s
  rfl

/-- A tuple-level target-add program over the explicit product field layout. -/
structure TupleTargetAddWitness {N n : Nat}
    (E : BinaryResidueEncoding N n) where
  /-- Program acting on the field tuple layout. -/
  program : BaseGateProgram (fieldTupleEncoding E).width
  /-- Correctness of the target-add program on tuple labels. -/
  realizes :
    BaseGateProgram.Realizes (fieldTupleEncoding E) program
      tupleAddQuotientToTarget

namespace TupleTargetAddWitness

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- Same-Circuit witness for the tuple-level target-add program. -/
def tupleWitness (w : TupleTargetAddWitness E) :
    BaseGateSameCircuitWitness (FieldTuple N) tupleAddQuotientToTarget where
  encoding := fieldTupleEncoding E
  program := w.program
  realizes := w.realizes

/-- Relabel a tuple-level target-add witness into the pipeline-state record
encoding used by the decomposed modular-division witness. -/
def pipelineWitness (w : TupleTargetAddWitness E) :
    BaseGateSameCircuitWitness (PipelineState N) addQuotientToTarget :=
  ((tupleWitness w).relabel (tupleEquiv N)).congrStep
    tupleAddQuotientToTarget_toPipeline

/-- The relabeled target-add program realizes `PipelineState.addQuotientToTarget`
on the pipeline-state field encoding. -/
theorem pipeline_realizes (w : TupleTargetAddWitness E) :
    BaseGateProgram.Realizes (fieldEncoding E) w.program addQuotientToTarget :=
  (pipelineWitness w).realizes

/-- Embed a modular-add target-update witness into the division field-tuple
layout by preserving the denominator and numerator fields. -/
def ofModularAddition (w : ModularAddition.TargetAddWithAux.Witness E) :
    TupleTargetAddWitness E where
  program :=
    (BaseGateSameCircuitWitness.prodRight
      (BinaryLabelEncoding.ofUnitResidueEncoding E)
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofResidueEncoding E) w.sameCircuit)).program
  realizes := by
    have h :=
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E)
        (BaseGateSameCircuitWitness.prodRight
          (BinaryLabelEncoding.ofResidueEncoding E) w.sameCircuit)).realizes
    change BaseGateProgram.Realizes
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E)
        (BaseGateSameCircuitWitness.prodRight
          (BinaryLabelEncoding.ofResidueEncoding E) w.sameCircuit)).encoding
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofUnitResidueEncoding E)
        (BaseGateSameCircuitWitness.prodRight
          (BinaryLabelEncoding.ofResidueEncoding E) w.sameCircuit)).program
      (fun x : (ZMod N)ˣ × (ZMod N × ModularAddition.TargetAddWithAux.Data N) =>
        (x.1, (x.2.1, ModularAddition.TargetAddWithAux.step x.2.2)))
    exact h

end TupleTargetAddWitness

/-! ## Power-of-two clean-work target-add-with-aux bridge -/

namespace PowerOfTwoTargetAddWithAux

/-- Carry-work labels for the VBE target-add-with-aux bridge used inside the
division pipeline layout [VBE95, 9511018.tex:237-264,591-618]. -/
abbrev CarryWork (n : Nat) : Type :=
  ModularAddition.TargetAddWithAux.PowerOfTwo.CarryWork n

/-- Distinguished clean carry-work label for the power-of-two
target-add-with-aux bridge. -/
def cleanWork (n : Nat) : CarryWork n :=
  (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).cleanWork

/-- Division field tuple plus target-add carry work.  The physical wire order is
denominator/numerator/target/inverse-scratch/quotient-scratch/flag/work,
matching the Proos--Zalka inverse/product/add/uncompute route with VBE carry
work made explicit [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:237-264,591-618]. -/
abbrev FieldTupleWithWork (n : Nat) : Type :=
  FieldTuple (2 ^ n) × CarryWork n

/-- Product reassociation between the division field tuple with trailing work
and the nested product shape required by two `prodRight` lifts. -/
def fieldTupleWithWorkEquiv (n : Nat) :
    FieldTupleWithWork n ≃
      ((ZMod (2 ^ n))ˣ ×
        (ZMod (2 ^ n) ×
          (ModularAddition.TargetAddWithAux.Data (2 ^ n) × CarryWork n))) where
  toFun := fun x => (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))
  invFun := fun x => ((x.1, (x.2.1, x.2.2.1)), x.2.2.2)
  left_inv := by
    intro x
    rcases x with ⟨⟨denominator, rest⟩, work⟩
    rcases rest with ⟨numerator, fields⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨denominator, rest⟩
    rcases rest with ⟨numerator, rest'⟩
    rcases rest' with ⟨fields, work⟩
    rfl

/-- Tuple-level target-add-with-aux with explicit carry work. -/
def tupleAddQuotientToTargetWithWork (n : Nat) :
    FieldTupleWithWork n -> FieldTupleWithWork n
  | ((denominator, (numerator, fields)), work) =>
      let y :=
        (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).stepWithWork
          (fields, work)
      ((denominator, (numerator, y.1)), y.2)

/-- Same-Circuit witness for tuple-level target-add-with-aux with explicit
carry work.  It is the lifted VBE target-add-with-aux base-gate program, so
correctness and resources are still attached to one gate object. -/
def tupleWithWorkSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (FieldTupleWithWork n)
      (tupleAddQuotientToTargetWithWork n) :=
  let targetAdd :=
    (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit
  let lifted :=
    BaseGateSameCircuitWitness.prodRight
      (BinaryLabelEncoding.ofUnitResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (BaseGateSameCircuitWitness.prodRight
        (BinaryLabelEncoding.ofResidueEncoding
          (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
        targetAdd)
  ((lifted.relabel (fieldTupleWithWorkEquiv n)).congrStep
    (by
      intro x
      rcases x with ⟨⟨denominator, rest⟩, work⟩
      rcases rest with ⟨numerator, fields⟩
      rfl))

/-- Clean tuple endpoint: on a clean flag and clean carry work, the work-aware
bridge agrees with the old tuple target-add action and restores work. -/
theorem tupleAddQuotientToTargetWithWork_cleanEndpoint
    (n : Nat) (x : FieldTuple (2 ^ n)) (hflag : x.2.2.2.2.2 = false) :
    tupleAddQuotientToTargetWithWork n (x, cleanWork n) =
      (tupleAddQuotientToTarget x, cleanWork n) := by
  rcases x with ⟨denominator, rest⟩
  rcases rest with ⟨numerator, fields⟩
  have h :=
    (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).cleanEndpoint
      fields hflag
  simpa [tupleAddQuotientToTargetWithWork, tupleAddQuotientToTarget, cleanWork]
    using congrArg (fun y => ((denominator, (numerator, y.1)), y.2)) h

/-- Division pipeline state plus carry work. -/
abbrev PipelineWithWork (n : Nat) : Type :=
  PipelineState (2 ^ n) × CarryWork n

/-- Relabel pipeline records to the tuple-with-work layout used by the lifted
target-add-with-aux circuit. -/
def pipelineWithWorkEquiv (n : Nat) :
    PipelineWithWork n ≃ FieldTupleWithWork n where
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

/-- Work-aware pipeline target-add step.  This is only the quotient-scratch
target-add leg of the Proos--Zalka division route, with VBE carry work explicit
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:237-264,591-618]. -/
def addQuotientToTargetWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n
  | (s, work) =>
      let y :=
        tupleAddQuotientToTargetWithWork n ((tupleEquiv (2 ^ n)) s, work)
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)

/-- Same-Circuit pipeline target-add witness with explicit carry work. -/
def pipelineWithWorkSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (PipelineWithWork n)
      (addQuotientToTargetWithWork n) :=
  ((tupleWithWorkSameCircuit n).relabel (pipelineWithWorkEquiv n)).congrStep
    (by
      intro x
      rcases x with ⟨s, work⟩
      rfl)

/-! ### Product-compute bit lenses -/

/-- Bit lens for an ordinary power-of-two residue field. -/
def productResidueBit (n : Nat) (bit : Fin n) :
    EncodedBit (BinaryLabelEncoding.ofResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n)) :=
  PlainAdder.Schedule.PowerOfTwo.wordBit n bit

@[simp] theorem productResidueBit_get_testBit
    (n : Nat) (bit : Fin n) (x : ZMod (2 ^ n)) :
    (productResidueBit n bit).get x = x.val.testBit bit.val := by
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get x =
    x.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit x

/-- Nested product encoding used before relabeling to `FieldTupleWithWork`.
The denominator is a unit field and is intentionally not exposed as an
`EncodedBit.Word`, because arbitrary bit flips need not preserve the unit
subtype. The quotient-product leg acts on numerator, inverse scratch, quotient
scratch, and target-add work [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:237-264,591-618]. -/
def productNestedEncoding (n : Nat) :
    BinaryLabelEncoding
      ((ZMod (2 ^ n))ˣ ×
        (ZMod (2 ^ n) ×
          (ModularAddition.TargetAddWithAux.Data (2 ^ n) × CarryWork n))) :=
  (BaseGateSameCircuitWitness.prodRight
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BaseGateSameCircuitWitness.prodRight
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit)).encoding

/-- Numerator bit lens in the nested division product layout. -/
def productNestedNumeratorBit (n : Nat) (bit : Fin n) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodLeftBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (productResidueBit n bit))

/-- Target bit lens in the nested division product layout. -/
def productNestedTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkTargetBit n bit))

/-- Inverse-scratch bit lens in the nested division product layout. -/
def productNestedInverseScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkAuxBit n bit))

/-- Quotient-scratch bit lens in the nested division product layout. -/
def productNestedQuotientScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkScratchBit n bit))

/-- Cleanup-flag bit lens in the nested division product layout. -/
def productNestedFlagBit (n : Nat) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkFlagBit n))

/-- Carry-work bit lens in the nested division product layout. -/
def productNestedCarryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (productNestedEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofUnitResidueEncoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding
        (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n))
      (ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness n).sameCircuit.encoding
      (ModularAddition.TargetAddWithAux.PowerOfTwo.carryWorkBit n bit))

/-- Numerator bit lens in the tuple-with-work division product layout. -/
def productTupleNumeratorBit (n : Nat) (bit : Fin n) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedNumeratorBit n bit).relabel (fieldTupleWithWorkEquiv n)

/-- Target bit lens in the tuple-with-work division product layout. -/
def productTupleTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedTargetBit n bit).relabel (fieldTupleWithWorkEquiv n)

/-- Inverse-scratch bit lens in the tuple-with-work division product layout. -/
def productTupleInverseScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedInverseScratchBit n bit).relabel (fieldTupleWithWorkEquiv n)

/-- Quotient-scratch bit lens in the tuple-with-work division product layout. -/
def productTupleQuotientScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedQuotientScratchBit n bit).relabel (fieldTupleWithWorkEquiv n)

/-- Cleanup-flag bit lens in the tuple-with-work division product layout. -/
def productTupleFlagBit (n : Nat) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedFlagBit n).relabel (fieldTupleWithWorkEquiv n)

/-- Carry-work bit lens in the tuple-with-work division product layout. -/
def productTupleCarryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (tupleWithWorkSameCircuit n).encoding :=
  (productNestedCarryWorkBit n bit).relabel (fieldTupleWithWorkEquiv n)

/-- Numerator bit lens in the work-aware division pipeline encoding. -/
def productNumeratorBit (n : Nat) (bit : Fin n) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleNumeratorBit n bit).relabel (pipelineWithWorkEquiv n)

/-- Target bit lens in the work-aware division pipeline encoding. -/
def productTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleTargetBit n bit).relabel (pipelineWithWorkEquiv n)

/-- Inverse-scratch bit lens in the work-aware division pipeline encoding. -/
def productInverseScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleInverseScratchBit n bit).relabel (pipelineWithWorkEquiv n)

/-- Quotient-scratch bit lens in the work-aware division pipeline encoding. -/
def productQuotientScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleQuotientScratchBit n bit).relabel (pipelineWithWorkEquiv n)

/-- Cleanup-flag bit lens in the work-aware division pipeline encoding. -/
def productFlagBit (n : Nat) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleFlagBit n).relabel (pipelineWithWorkEquiv n)

/-- Carry-work bit lens in the work-aware division pipeline encoding. -/
def productCarryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (pipelineWithWorkSameCircuit n).encoding :=
  (productTupleCarryWorkBit n bit).relabel (pipelineWithWorkEquiv n)

/-- Numerator word lens for the quotient-product compute leg. -/
def productNumeratorWord (n : Nat) :
    EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding n where
  bit := productNumeratorBit n

/-- Target word lens for the quotient-product compute leg. -/
def productTargetWord (n : Nat) :
    EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding n where
  bit := productTargetBit n

/-- Inverse-scratch word lens for the quotient-product compute leg. -/
def productInverseScratchWord (n : Nat) :
    EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding n where
  bit := productInverseScratchBit n

/-- Quotient-scratch word lens for the quotient-product compute leg. -/
def productQuotientScratchWord (n : Nat) :
    EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding n where
  bit := productQuotientScratchBit n

/-- Carry-work word lens for the quotient-product compute leg. -/
def productCarryWorkWord (n : Nat) :
    EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding (n - 1) where
  bit := productCarryWorkBit n

@[simp] theorem productNumeratorBit_wire_val (n : Nat) (bit : Fin n) :
    ((productNumeratorBit n bit).wire).val =
      n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem productTargetBit_wire_val (n : Nat) (bit : Fin n) :
    ((productTargetBit n bit).wire).val =
      n + (n + (n - 1 - bit.val)) := by
  rfl

@[simp] theorem productInverseScratchBit_wire_val (n : Nat) (bit : Fin n) :
    ((productInverseScratchBit n bit).wire).val =
      n + (n + (n + (n - 1 - bit.val))) := by
  rfl

@[simp] theorem productQuotientScratchBit_wire_val (n : Nat) (bit : Fin n) :
    ((productQuotientScratchBit n bit).wire).val =
      n + (n + (n + (n + (n - 1 - bit.val)))) := by
  rfl

@[simp] theorem productFlagBit_wire_val (n : Nat) :
    ((productFlagBit n).wire).val = n + (n + (n + (n + n))) := by
  rfl

@[simp] theorem productCarryWorkBit_wire_val (n : Nat) (bit : Fin (n - 1)) :
    ((productCarryWorkBit n bit).wire).val =
      n + (n + (n + (n + (n + 1 + bit.val)))) := by
  change n + (n +
      ((ModularAddition.TargetAddWithAux.PowerOfTwo.carryWorkBit n bit).wire).val) =
    n + (n + (n + (n + (n + 1 + bit.val))))
  rw [ModularAddition.TargetAddWithAux.PowerOfTwo.carryWorkBit_wire_val]
  rw [ModularAddition.TargetAddWithAux.PowerOfTwo.targetAuxEncoding_width]
  omega

/-- The numerator and inverse-scratch fields occupy disjoint wire slices in
the quotient-product layout. -/
theorem productInverseScratchBit_ne_numerator
    (n : Nat) (control source : Fin n) :
    ((productInverseScratchWord n).bit control).wire ≠
      ((productNumeratorWord n).bit source).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hcontrol := control.isLt
  have hsource := source.isLt
  simp [productInverseScratchWord, productNumeratorWord] at hv
  omega

/-- Inverse-scratch wires are disjoint from quotient-scratch wires. -/
theorem productInverseScratchBit_ne_quotientScratch
    (n : Nat) (inverseBit quotientBit : Fin n) :
    ((productInverseScratchWord n).bit inverseBit).wire ≠
      ((productQuotientScratchWord n).bit quotientBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hinverse := inverseBit.isLt
  have hquotient := quotientBit.isLt
  simp [productInverseScratchWord, productQuotientScratchWord] at hv
  omega

/-- Numerator wires are disjoint from quotient-scratch wires. -/
theorem productNumeratorBit_ne_quotientScratch
    (n : Nat) (numeratorBit quotientBit : Fin n) :
    ((productNumeratorWord n).bit numeratorBit).wire ≠
      ((productQuotientScratchWord n).bit quotientBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hnumerator := numeratorBit.isLt
  have hquotient := quotientBit.isLt
  simp [productNumeratorWord, productQuotientScratchWord] at hv
  omega

/-- Inverse-scratch wires are disjoint from carry-work wires. -/
theorem productInverseScratchBit_ne_carryWork
    (n : Nat) (inverseBit : Fin n) (carryBit : Fin (n - 1)) :
    ((productInverseScratchWord n).bit inverseBit).wire ≠
      ((productCarryWorkWord n).bit carryBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hinverse := inverseBit.isLt
  have hcarry := carryBit.isLt
  simp [productInverseScratchWord, productCarryWorkWord] at hv
  omega

/-- Numerator wires are disjoint from carry-work wires. -/
theorem productNumeratorBit_ne_carryWork
    (n : Nat) (numeratorBit : Fin n) (carryBit : Fin (n - 1)) :
    ((productNumeratorWord n).bit numeratorBit).wire ≠
      ((productCarryWorkWord n).bit carryBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hnumerator := numeratorBit.isLt
  have hcarry := carryBit.isLt
  simp [productNumeratorWord, productCarryWorkWord] at hv
  omega

/-- Distinct quotient-scratch bit positions occupy distinct wires. -/
theorem productQuotientScratchBit_ne
    (n : Nat) {i j : Fin n} (hij : i ≠ j) :
    ((productQuotientScratchWord n).bit i).wire ≠
      ((productQuotientScratchWord n).bit j).wire := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [productQuotientScratchWord] at hv
  omega

/-- Quotient-scratch wires are disjoint from the cleanup flag. -/
theorem productQuotientScratchBit_ne_flag (n : Nat) (i : Fin n) :
    ((productQuotientScratchWord n).bit i).wire ≠ (productFlagBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp [productQuotientScratchWord] at hv
  omega

/-- Quotient-scratch wires are disjoint from carry-work wires. -/
theorem productQuotientScratchBit_ne_carryWork
    (n : Nat) (i : Fin n) (j : Fin (n - 1)) :
    ((productQuotientScratchWord n).bit i).wire ≠
      ((productCarryWorkWord n).bit j).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp [productQuotientScratchWord, productCarryWorkWord] at hv
  omega

/-- Quotient-scratch wires are disjoint from target wires. -/
theorem productQuotientScratchBit_ne_target
    (n : Nat) (quotientBit targetBit : Fin n) :
    ((productQuotientScratchWord n).bit quotientBit).wire ≠
      ((productTargetWord n).bit targetBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hquotient := quotientBit.isLt
  have htarget := targetBit.isLt
  simp [productQuotientScratchWord, productTargetWord] at hv
  omega

/-- The cleanup flag is disjoint from carry-work wires. -/
theorem productFlagBit_ne_carryWork
    (n : Nat) (j : Fin (n - 1)) :
    (productFlagBit n).wire ≠ ((productCarryWorkWord n).bit j).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp [productCarryWorkWord] at hv
  omega

/-- Carry-work wires are disjoint from target wires. -/
theorem productCarryWorkBit_ne_target
    (n : Nat) (carryBit : Fin (n - 1)) (targetBit : Fin n) :
    ((productCarryWorkWord n).bit carryBit).wire ≠
      ((productTargetWord n).bit targetBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hcarry := carryBit.isLt
  have htarget := targetBit.isLt
  simp [productCarryWorkWord, productTargetWord] at hv
  omega

/-- Distinct carry-work bit positions occupy distinct wires. -/
theorem productCarryWorkBit_ne
    (n : Nat) {i j : Fin (n - 1)} (hij : i ≠ j) :
    ((productCarryWorkWord n).bit i).wire ≠
      ((productCarryWorkWord n).bit j).wire := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [productCarryWorkWord] at hv
  omega

/-! ### Product-compute workspace interface -/

/-- Work-aware division pipeline plus an explicit product-compute workspace.
This keeps extra scratch needed by a future quotient-product circuit visible
instead of hiding it in the proof of `productRealizes` [PZ03, ecc.tex:622-640;
VBE95, 9511018.tex:333-350]. -/
abbrev PipelineWithProductWork (n : Nat) (ProductWork : Type) : Type :=
  PipelineWithWork n × ProductWork

/-- Encoding for a division pipeline with explicit product-compute workspace. -/
def pipelineWithProductWorkEncoding (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    BinaryLabelEncoding (PipelineWithProductWork n ProductWork) :=
  (BaseGateSameCircuitWitness.prodLeft (pipelineWithWorkSameCircuit n)
    productEncoding).encoding

/-! #### One-row product workspace -/

/-- One clean product-row workspace for a controlled shifted product-row
update.  A full product circuit can load one shifted partial product into this
row, reuse the ordinary clean carry-work adder, then unload the row
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
abbrev ProductRowWork (n : Nat) : Type :=
  ZMod (2 ^ n)

/-- A power-of-two residue is the sum of the powers of two selected by the
canonical natural representative's bit indices. -/
theorem zmod_twoPow_eq_sum_bitIndices (n : Nat) (a : ProductRowWork n) :
    a =
      ∑ i ∈ a.val.bitIndices.toFinset,
        ((2 ^ i : Nat) : ProductRowWork n) := by
  calc
    a = ((a.val : Nat) : ProductRowWork n) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    _ =
        ((∑ i ∈ a.val.bitIndices.toFinset, 2 ^ i : Nat) :
          ProductRowWork n) := by
      rw [Finset.sum_toFinset_bitIndices_two_pow]
    _ =
        ∑ i ∈ a.val.bitIndices.toFinset,
          ((2 ^ i : Nat) : ProductRowWork n) := by
      exact Nat.cast_sum
        (R := ProductRowWork n) (s := a.val.bitIndices.toFinset)
        (f := fun i => 2 ^ i)

/-- A power `2^k` with `n <= k` vanishes in `ZMod (2^n)`. -/
theorem zmod_twoPow_natCast_twoPow_eq_zero_of_le
    (n k : Nat) (h : n ≤ k) :
    ((2 ^ k : Nat) : ProductRowWork n) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow 2 h

/-- Casting a natural number into `ZMod (2^n)` preserves all low `n` bits. -/
theorem zmod_twoPow_natCast_val_testBit
    (n m : Nat) (bit : Fin n) :
    (((m : Nat) : ProductRowWork n).val.testBit bit.val) =
      m.testBit bit.val := by
  rw [ZMod.val_natCast]
  rw [Nat.testBit_mod_two_pow]
  simp [bit.isLt]

/-- Low-bit readout for a shifted natural number cast into `ZMod (2^n)`. -/
theorem zmod_twoPow_natCast_shifted_val_testBit
    (n m offset : Nat) (target : Fin n) :
    (((m * 2 ^ offset : Nat) : ProductRowWork n).val.testBit target.val) =
      (decide (target.val ≥ offset) && m.testBit (target.val - offset)) := by
  rw [← Nat.shiftLeft_eq]
  rw [zmod_twoPow_natCast_val_testBit]
  exact Nat.testBit_shiftLeft m

/-- Multiplication in a power-of-two residue ring expands into the double sum
over the two canonical bit-index sets. -/
theorem zmod_twoPow_mul_eq_sum_bitIndices
    (n : Nat) (a b : ProductRowWork n) :
    a * b =
      ∑ i ∈ a.val.bitIndices.toFinset,
        ∑ j ∈ b.val.bitIndices.toFinset,
          ((2 ^ (i + j) : Nat) : ProductRowWork n) := by
  calc
    a * b =
        (∑ i ∈ a.val.bitIndices.toFinset,
            ((2 ^ i : Nat) : ProductRowWork n)) *
          (∑ j ∈ b.val.bitIndices.toFinset,
            ((2 ^ j : Nat) : ProductRowWork n)) := by
      exact congrArg₂ (fun x y : ProductRowWork n => x * y)
        (zmod_twoPow_eq_sum_bitIndices n a)
        (zmod_twoPow_eq_sum_bitIndices n b)
    _ =
        ∑ i ∈ a.val.bitIndices.toFinset,
          ∑ j ∈ b.val.bitIndices.toFinset,
            ((2 ^ i : Nat) : ProductRowWork n) *
              ((2 ^ j : Nat) : ProductRowWork n) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    _ =
        ∑ i ∈ a.val.bitIndices.toFinset,
          ∑ j ∈ b.val.bitIndices.toFinset,
            ((2 ^ (i + j) : Nat) : ProductRowWork n) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← Nat.cast_mul, ← pow_add]

/-- The same multiplication expansion with the terms outside the low `n`
output bits written as explicit zeros. -/
theorem zmod_twoPow_mul_eq_sum_low_bitIndices
    (n : Nat) (a b : ProductRowWork n) :
    a * b =
      ∑ i ∈ a.val.bitIndices.toFinset,
        ∑ j ∈ b.val.bitIndices.toFinset,
          if _h : i + j < n then
            ((2 ^ (i + j) : Nat) : ProductRowWork n)
          else
            0 := by
  rw [zmod_twoPow_mul_eq_sum_bitIndices n a b]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases h : i + j < n
  · simp [h]
  · have hle : n ≤ i + j := Nat.le_of_not_gt h
    simp [h, zmod_twoPow_natCast_twoPow_eq_zero_of_le n (i + j) hle]

private theorem productRowWork_bitIndex_lt
    {n i : Nat} (a : ProductRowWork n)
    (hi : i ∈ a.val.bitIndices) : i < n := by
  by_contra hlt
  have hni : n ≤ i := Nat.le_of_not_gt hlt
  have hpow_le : 2 ^ n ≤ 2 ^ i :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hni
  have hi_le : 2 ^ i ≤ a.val := Nat.two_pow_le_of_mem_bitIndices hi
  exact (Nat.not_le_of_gt (ZMod.val_lt a)) (le_trans hpow_le hi_le)

/-- Multiplication by a residue equals the sum of shifted copies selected by
that residue's low-bit set. -/
theorem zmod_twoPow_mul_eq_sum_shifted_bitIndices
    (n : Nat) (a b : ProductRowWork n) :
    a * b =
      ∑ j ∈ b.val.bitIndices.toFinset,
        ((a.val * 2 ^ j : Nat) : ProductRowWork n) := by
  calc
    a * b =
        a * (∑ j ∈ b.val.bitIndices.toFinset,
          ((2 ^ j : Nat) : ProductRowWork n)) := by
      exact congrArg (fun y : ProductRowWork n => a * y)
        (zmod_twoPow_eq_sum_bitIndices n b)
    _ =
        ∑ j ∈ b.val.bitIndices.toFinset,
          a * ((2 ^ j : Nat) : ProductRowWork n) := by
      rw [Finset.mul_sum]
    _ =
        ∑ j ∈ b.val.bitIndices.toFinset,
          ((a.val * 2 ^ j : Nat) : ProductRowWork n) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      rw [← Nat.cast_mul]

/-- A full `Fin n` sum of shifted copies selected by low bits is the same sum
over the canonical bit-index set. -/
theorem zmod_twoPow_shiftedBitSum_eq_sum_bitIndices
    (n : Nat) (a b : ProductRowWork n) :
    (∑ offset : Fin n,
        if b.val.testBit offset.val then
          ((a.val * 2 ^ offset.val : Nat) : ProductRowWork n)
        else
          0) =
      ∑ j ∈ b.val.bitIndices.toFinset,
        ((a.val * 2 ^ j : Nat) : ProductRowWork n) := by
  classical
  have hsum :
      (Finset.univ.filter
        (fun offset : Fin n => b.val.testBit offset.val)).sum
          (fun offset : Fin n =>
            ((a.val * 2 ^ offset.val : Nat) : ProductRowWork n)) =
        b.val.bitIndices.toFinset.sum
          (fun j : Nat => ((a.val * 2 ^ j : Nat) : ProductRowWork n)) := by
    refine Finset.sum_bij (fun offset _ => offset.val) ?_ ?_ ?_ ?_
    · intro offset hoffset
      rw [List.mem_toFinset]
      rw [Nat.mem_bitIndices]
      exact (Finset.mem_filter.mp hoffset).2
    · intro offset₁ _ offset₂ _ hval
      exact Fin.ext hval
    · intro j hj
      rw [List.mem_toFinset] at hj
      have hjlt : j < n := productRowWork_bitIndex_lt b hj
      refine ⟨⟨j, hjlt⟩, ?_, rfl⟩
      simp [Nat.mem_bitIndices.mp hj]
    · intro offset _
      rfl
  simpa [Finset.sum_filter] using hsum

/-- A full `Fin n` sum of shifted copies selected by low bits is multiplication
in `ZMod (2^n)`. -/
theorem zmod_twoPow_shiftedBitSum_eq_mul
    (n : Nat) (a b : ProductRowWork n) :
    (∑ offset : Fin n,
        if b.val.testBit offset.val then
          ((a.val * 2 ^ offset.val : Nat) : ProductRowWork n)
        else
          0) =
      a * b := by
  rw [zmod_twoPow_shiftedBitSum_eq_sum_bitIndices,
    ← zmod_twoPow_mul_eq_sum_shifted_bitIndices]

/-- Binary residue encoding for the product-row workspace. -/
def productRowEncoding (n : Nat) :
    BinaryLabelEncoding (ProductRowWork n) :=
  BinaryLabelEncoding.ofResidueEncoding
    (ModularAddition.TargetAddWithAux.PowerOfTwo.residueEncoding n)

/-- Distinguished clean product-row workspace value. -/
def cleanProductRowWork (n : Nat) : ProductRowWork n :=
  0

/-- Product-row bit lens before lifting into the full product-workspace
layout. -/
def productRowBit (n : Nat) (bit : Fin n) :
    EncodedBit (productRowEncoding n) :=
  productResidueBit n bit

/-- Product-row word lens before lifting into the full product-workspace
layout. -/
def productRowWord (n : Nat) :
    EncodedBit.Word (productRowEncoding n) n where
  bit := productRowBit n

@[simp] theorem productRowBit_wire_val (n : Nat) (bit : Fin n) :
    ((productRowBit n bit).wire).val = n - 1 - bit.val := by
  rfl

/-- Distinct product-row bit positions occupy distinct wires. -/
theorem productRowBit_ne
    (n : Nat) {i j : Fin n} (hij : i ≠ j) :
    ((productRowWord n).bit i).wire ≠
      ((productRowWord n).bit j).wire := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [productRowWord] at hv
  omega

/-- Division pipeline with the one-row product workspace selected for the next
quotient-product circuit slice. -/
abbrev PipelineWithProductRowWork (n : Nat) : Type :=
  PipelineWithProductWork n (ProductRowWork n)

/-- Encoding for the division pipeline with one clean product row. -/
def pipelineWithProductRowWorkEncoding (n : Nat) :
    BinaryLabelEncoding (PipelineWithProductRowWork n) :=
  pipelineWithProductWorkEncoding n (productRowEncoding n)

/-- The product-row pipeline has a concrete clean label, needed when choosing
`Function.invFun` for the semantic inverse of a finite reversible program. -/
instance instNonemptyPipelineWithProductRowWork (n : Nat) :
    Nonempty (PipelineWithProductRowWork n) :=
  ⟨((initial (N := 2 ^ n) (1 : (ZMod (2 ^ n))ˣ) 0 0,
      cleanWork n),
    cleanProductRowWork n)⟩

/-- Lift a pipeline-register bit lens over explicit product-compute workspace. -/
def productWorkspacePipelineBit (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork)
    (bit : EncodedBit (pipelineWithWorkSameCircuit n).encoding) :
    EncodedBit (pipelineWithProductWorkEncoding n productEncoding) :=
  BinaryLabelEncoding.prodLeftBit (pipelineWithWorkSameCircuit n).encoding
    productEncoding bit

/-- Lift a product-work bit lens into the full pipeline/product-work layout. -/
def productWorkspaceBit (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork)
    (bit : EncodedBit productEncoding) :
    EncodedBit (pipelineWithProductWorkEncoding n productEncoding) :=
  BinaryLabelEncoding.prodRightBit (pipelineWithWorkSameCircuit n).encoding
    productEncoding bit

/-- Lift a pipeline-register word lens over explicit product-compute workspace. -/
def productWorkspacePipelineWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) {width : Nat}
    (word : EncodedBit.Word (pipelineWithWorkSameCircuit n).encoding width) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) width where
  bit := fun i => productWorkspacePipelineBit n productEncoding (word.bit i)

/-- Lift a product-work word lens into the full pipeline/product-work layout. -/
def productWorkspaceWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) {width : Nat}
    (word : EncodedBit.Word productEncoding width) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) width where
  bit := fun i => productWorkspaceBit n productEncoding (word.bit i)

/-- Numerator word lens in the full product-workspace layout.  This is the
source word for the controlled shifted-copy layer used by quotient-product
computation [PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
def productWorkspaceNumeratorWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) n :=
  productWorkspacePipelineWord n productEncoding (productNumeratorWord n)

/-- Inverse-scratch word lens in the full product-workspace layout.  Its bits
select the controlled shifted-copy stages for quotient-product computation
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
def productWorkspaceInverseScratchWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) n :=
  productWorkspacePipelineWord n productEncoding (productInverseScratchWord n)

/-- Target word lens in the full product-workspace layout. -/
def productWorkspaceTargetWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) n :=
  productWorkspacePipelineWord n productEncoding (productTargetWord n)

/-- Quotient-scratch word lens in the full product-workspace layout. -/
def productWorkspaceQuotientScratchWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) n :=
  productWorkspacePipelineWord n productEncoding (productQuotientScratchWord n)

/-- Carry-work word lens in the full product-workspace layout. -/
def productWorkspaceCarryWorkWord (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit.Word (pipelineWithProductWorkEncoding n productEncoding) (n - 1) :=
  productWorkspacePipelineWord n productEncoding (productCarryWorkWord n)

/-- Cleanup-flag bit lens in the full product-workspace layout. -/
def productWorkspaceFlagBit (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork) :
    EncodedBit (pipelineWithProductWorkEncoding n productEncoding) :=
  productWorkspacePipelineBit n productEncoding (productFlagBit n)

/-- Numerator word lens in the one-row product-workspace layout. -/
def productRowWorkspaceNumeratorWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n :=
  productWorkspaceNumeratorWord n (productRowEncoding n)

/-- Inverse-scratch word lens in the one-row product-workspace layout. -/
def productRowWorkspaceInverseScratchWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n :=
  productWorkspaceInverseScratchWord n (productRowEncoding n)

/-- Target word lens in the one-row product-workspace layout. -/
def productRowWorkspaceTargetWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n :=
  productWorkspaceTargetWord n (productRowEncoding n)

/-- Quotient-scratch word lens in the one-row product-workspace layout. -/
def productRowWorkspaceQuotientScratchWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n :=
  productWorkspaceQuotientScratchWord n (productRowEncoding n)

@[simp] theorem productRowWorkspaceNumeratorBit_get_testBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit bit).get x =
      x.1.1.numerator.val.testBit bit.val := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  change (productTupleNumeratorBit n bit).get
      (((tupleEquiv (2 ^ n))
        { denominator := den
          numerator := num
          target := tgt
          inverseScratch := inv
          quotientScratch := qs
          flag := flg }), work) =
    num.val.testBit bit.val
  exact productResidueBit_get_testBit n bit num

@[simp] theorem productRowWorkspaceInverseScratchBit_get_testBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit bit).get x =
      x.1.1.inverseScratch.val.testBit bit.val := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  change (productTupleInverseScratchBit n bit).get
      (((tupleEquiv (2 ^ n))
        { denominator := den
          numerator := num
          target := tgt
          inverseScratch := inv
          quotientScratch := qs
          flag := flg }), work) =
    inv.val.testBit bit.val
  exact ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkAuxBit_get_fst
    n bit ((tgt, (inv, (qs, flg))), work)

@[simp] theorem productRowWorkspaceTargetBit_get_testBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit bit).get x =
      x.1.1.target.val.testBit bit.val := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  change (productTupleTargetBit n bit).get
      (((tupleEquiv (2 ^ n))
        { denominator := den
          numerator := num
          target := tgt
          inverseScratch := inv
          quotientScratch := qs
          flag := flg }), work) =
    tgt.val.testBit bit.val
  exact ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkTargetBit_get_fst
    n bit ((tgt, (inv, (qs, flg))), work)

@[simp] theorem productRowWorkspaceQuotientScratchBit_get_testBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceQuotientScratchWord n).bit bit).get x =
      x.1.1.quotientScratch.val.testBit bit.val := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  change (productTupleQuotientScratchBit n bit).get
      (((tupleEquiv (2 ^ n))
        { denominator := den
          numerator := num
          target := tgt
          inverseScratch := inv
          quotientScratch := qs
          flag := flg }), work) =
    qs.val.testBit bit.val
  exact ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkScratchBit_get_fst
    n bit ((tgt, (inv, (qs, flg))), work)

@[simp] theorem productRowWorkspaceQuotientScratchBit_flip_denominator
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    (((productRowWorkspaceQuotientScratchWord n).bit bit).flip x).1.1.denominator =
      x.1.1.denominator := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  rfl

/-- Carry-work word lens in the one-row product-workspace layout. -/
def productRowWorkspaceCarryWorkWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) (n - 1) :=
  productWorkspaceCarryWorkWord n (productRowEncoding n)

@[simp] theorem productRowWorkspaceCarryWorkBit_get_snd
    (n : Nat) (bit : Fin (n - 1)) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit bit).get x =
      (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get x.1.2 := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  rfl

theorem productRowWorkspaceCarryWorkBit_get_clean
    (n : Nat) (bit : Fin (n - 1))
    (s : PipelineState (2 ^ n)) (row : ProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit bit).get
        ((s, cleanWork n), row) = false := by
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (0 : Fin (2 ^ (n - 1))) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero (n - 1) bit

/-- A product-row pipeline has clean target-add carry work when all carry-work
bits read `false` in the concrete product-row layout. -/
theorem productRowWorkspaceCarryWork_eq_clean_of_get_false
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    x.1.2 = cleanWork n := by
  apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
  intro bit
  simpa [PowerOfTwoTargetAddWithAux.cleanWork,
    ModularAddition.TargetAddWithAux.PowerOfTwo.cleanWorkWitness,
    ModularAddition.TargetAddWithAux.PowerOfTwo.cleanCarryWork] using hwork bit

@[simp] theorem productRowWorkspaceCarryWorkBit_flip_denominator
    (n : Nat) (bit : Fin (n - 1)) (x : PipelineWithProductRowWork n) :
    (((productRowWorkspaceCarryWorkWord n).bit bit).flip x).1.1.denominator =
      x.1.1.denominator := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  rfl

/-- Cleanup-flag bit lens in the one-row product-workspace layout. -/
def productRowWorkspaceFlagBit (n : Nat) :
    EncodedBit (pipelineWithProductRowWorkEncoding n) :=
  productWorkspaceFlagBit n (productRowEncoding n)

@[simp] theorem productRowWorkspaceFlagBit_get_flag
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get x = x.1.1.flag := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  change (productTupleFlagBit n).get
      (((tupleEquiv (2 ^ n))
        { denominator := den
          numerator := num
          target := tgt
          inverseScratch := inv
          quotientScratch := qs
          flag := flg }), work) =
    flg
  exact ModularAddition.TargetAddWithAux.PowerOfTwo.withCarryWorkFlagBit_get_fst
    n ((tgt, (inv, (qs, flg))), work)

/-- Product-row word lens in the one-row product-workspace layout. -/
def productRowWorkspaceRowWord (n : Nat) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n :=
  productWorkspaceWord n (productRowEncoding n) (productRowWord n)

@[simp] theorem productRowWorkspaceRowBit_get_testBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit bit).get x =
      x.2.val.testBit bit.val := by
  rcases x with ⟨pipeline, row⟩
  change (productRowBit n bit).get row = row.val.testBit bit.val
  exact productResidueBit_get_testBit n bit row

@[simp] theorem productRowWorkspaceRowBit_flip_denominator
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    (((productRowWorkspaceRowWord n).bit bit).flip x).1.1.denominator =
      x.1.1.denominator := by
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, qs, flg⟩
  rfl

/-! #### Controlled shifted product-row load -/

/-- Cyclic target index for loading a shifted partial-product row over the
`n` bit positions. -/
def shiftedRowIndex {n : Nat} (offset bit : Fin n) : Fin n :=
  ⟨(bit.val + offset.val) % n,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le offset.val) offset.isLt)⟩

/-- Cyclic row shifts are injective on bit positions. -/
theorem shiftedRowIndex_injective {n : Nat} (offset : Fin n) :
    Function.Injective (shiftedRowIndex offset) := by
  intro i j h
  apply Fin.ext
  have hmod :
      (i.val + offset.val) % n = (j.val + offset.val) % n :=
    congrArg Fin.val h
  have hmodeq :
      i.val + offset.val ≡ j.val + offset.val [MOD n] := by
    simpa [Nat.ModEq] using hmod
  have hcancel : i.val ≡ j.val [MOD n] :=
    Nat.ModEq.add_right_cancel' offset.val hmodeq
  have hi : i.val % n = i.val := Nat.mod_eq_of_lt i.isLt
  have hj : j.val % n = j.val := Nat.mod_eq_of_lt j.isLt
  simpa [Nat.ModEq, hi, hj] using hcancel

/-- Distinct bit positions remain distinct after a cyclic row shift. -/
theorem shiftedRowIndex_ne {n : Nat} (offset : Fin n) {i j : Fin n}
    (hij : i ≠ j) :
    shiftedRowIndex offset i ≠ shiftedRowIndex offset j :=
  fun h => hij (shiftedRowIndex_injective offset h)

/-- Cyclic row shifts cover every bit position. -/
theorem shiftedRowIndex_surjective {n : Nat} (offset : Fin n) :
    Function.Surjective (shiftedRowIndex offset) :=
  (Finite.injective_iff_surjective).mp (shiftedRowIndex_injective offset)

/-- Non-wrapping target index for a low-bit shifted partial product. -/
def truncatedShiftedRowIndex {n : Nat} (offset bit : Fin n)
    (h : bit.val + offset.val < n) : Fin n :=
  ⟨bit.val + offset.val, h⟩

/-- Source bits whose shifted partial-product target remains inside the low
`n` output bits. -/
def truncatedShiftedRowSources (n : Nat) (offset : Fin n) : List (Fin n) :=
  (List.ofFn fun bit : Fin n => bit).filter
    (fun bit => bit.val + offset.val < n)

/-- The valid non-wrapping shifted sources have no duplicates. -/
theorem truncatedShiftedRowSources_nodup
    (n : Nat) (offset : Fin n) :
    (truncatedShiftedRowSources n offset).Nodup := by
  unfold truncatedShiftedRowSources
  exact (List.nodup_ofFn_ofInjective (fun _ _ h => h)).filter _

/-- Membership in the non-wrapping shifted-source list is exactly the
low-output-bit overflow check. -/
theorem mem_truncatedShiftedRowSources
    (n : Nat) (offset bit : Fin n) :
    bit ∈ truncatedShiftedRowSources n offset ↔
      bit.val + offset.val < n := by
  simp [truncatedShiftedRowSources]

/-- Non-wrapping shifted target indices are injective on valid source bits. -/
theorem truncatedShiftedRowIndex_injective {n : Nat} (offset : Fin n)
    {i j : Fin n} (hi : i.val + offset.val < n)
    (hj : j.val + offset.val < n)
    (hij : truncatedShiftedRowIndex offset i hi =
      truncatedShiftedRowIndex offset j hj) :
    i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp [truncatedShiftedRowIndex] at hv
  omega

/-- Product-row word lens with indices shifted by `offset`. -/
def productRowWorkspaceShiftedRowWord (n : Nat) (offset : Fin n) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n where
  bit := fun i => (productRowWorkspaceRowWord n).bit (shiftedRowIndex offset i)

/-- Target word for the non-wrapping low-bit partial-product load.  Invalid
indices are assigned an arbitrary row bit because the folded index list never
executes them; the injectivity lemmas below are intentionally stated only over
`truncatedShiftedRowSources`. -/
def productRowWorkspaceTruncatedShiftedRowWord (n : Nat) (offset : Fin n) :
    EncodedBit.Word (pipelineWithProductRowWorkEncoding n) n where
  bit := fun i =>
    if h : i.val + offset.val < n then
      (productRowWorkspaceRowWord n).bit
        (truncatedShiftedRowIndex offset i h)
    else
      (productRowWorkspaceRowWord n).bit i

@[simp] theorem productRowWorkspaceShiftedRowBit_flip_denominator
    (n : Nat) (offset bit : Fin n) (x : PipelineWithProductRowWork n) :
    (((productRowWorkspaceShiftedRowWord n offset).bit bit).flip x).1.1.denominator =
      x.1.1.denominator := by
  simp [productRowWorkspaceShiftedRowWord]

@[simp] theorem productRowWorkspaceTruncatedShiftedRowBit_flip_denominator
    (n : Nat) (offset bit : Fin n) (x : PipelineWithProductRowWork n) :
    (((productRowWorkspaceTruncatedShiftedRowWord n offset).bit bit).flip
        x).1.1.denominator =
      x.1.1.denominator := by
  unfold productRowWorkspaceTruncatedShiftedRowWord
  by_cases h : bit.val + offset.val < n <;> simp [h]

/-- Pipeline-register wires are disjoint from trailing product-work wires in
the product-workspace encoding. -/
theorem productWorkspacePipelineBit_ne_productBit
    (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork)
    (pipelineBit : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (workBit : EncodedBit productEncoding) :
    (productWorkspacePipelineBit n productEncoding pipelineBit).wire ≠
      (productWorkspaceBit n productEncoding workBit).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hpipeline := pipelineBit.wire.isLt
  simp [productWorkspacePipelineBit, productWorkspaceBit,
    pipelineWithProductWorkEncoding, BaseGateSameCircuitWitness.prodLeft,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire] at hv
  omega

/-- Lifting two pipeline-register bits over product workspace preserves wire
separation. -/
theorem productWorkspacePipelineBit_ne_of_ne
    (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork)
    (left right : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (hne : left.wire ≠ right.wire) :
    (productWorkspacePipelineBit n productEncoding left).wire ≠
      (productWorkspacePipelineBit n productEncoding right).wire := by
  intro h
  apply hne
  apply Fin.ext
  have hv0 := congrArg Fin.val h
  simpa only [productWorkspacePipelineBit, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodLeftWire] using hv0

/-- Lifting two product-work bits into the full product workspace preserves
wire separation. -/
theorem productWorkspaceBit_ne_of_ne
    (n : Nat) {ProductWork : Type}
    (productEncoding : BinaryLabelEncoding ProductWork)
    (left right : EncodedBit productEncoding)
    (hne : left.wire ≠ right.wire) :
    (productWorkspaceBit n productEncoding left).wire ≠
      (productWorkspaceBit n productEncoding right).wire := by
  intro h
  apply hne
  apply Fin.ext
  have hv0 := congrArg Fin.val h
  have hv :
      left.wire.val = right.wire.val := by
    simp only [productWorkspaceBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodRightWire] at hv0
    omega
  exact hv

/-- Inverse-scratch controls are disjoint from numerator sources in the
one-row product-workspace layout. -/
theorem productRowWorkspaceInverseScratch_ne_numerator
    (n : Nat) (offset i : Fin n) :
    ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
      ((productRowWorkspaceNumeratorWord n).bit i).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit offset)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).wire
  intro h
  have hv0 := congrArg Fin.val h
  have hv :
      ((productInverseScratchWord n).bit offset).wire.val =
        ((productNumeratorWord n).bit i).wire.val := by
    simpa only [productWorkspacePipelineBit, BinaryLabelEncoding.prodLeftBit,
      BinaryLabelEncoding.prodLeftWire] using hv0
  exact productInverseScratchBit_ne_numerator n offset i (Fin.ext hv)

/-- Inverse-scratch controls are disjoint from shifted product-row targets. -/
theorem productRowWorkspaceInverseScratch_ne_shiftedRow
    (n : Nat) (offset i : Fin n) :
    ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
      ((productRowWorkspaceShiftedRowWord n offset).bit i).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit offset)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit (shiftedRowIndex offset i))).wire
  exact
    productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
      ((productInverseScratchWord n).bit offset)
      ((productRowWord n).bit (shiftedRowIndex offset i))

/-- Inverse-scratch controls are disjoint from any product-row target bit. -/
theorem productRowWorkspaceInverseScratch_ne_rowBit
    (n : Nat) (offset target : Fin n) :
    ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
      ((productRowWorkspaceRowWord n).bit target).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit offset)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit target)).wire
  exact
    productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
      ((productInverseScratchWord n).bit offset)
      ((productRowWord n).bit target)

/-- Numerator source wires are disjoint from shifted product-row targets. -/
theorem productRowWorkspaceNumerator_ne_shiftedRow
    (n : Nat) (offset i : Fin n) :
    ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
      ((productRowWorkspaceShiftedRowWord n offset).bit i).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit (shiftedRowIndex offset i))).wire
  exact
    productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
      ((productNumeratorWord n).bit i)
      ((productRowWord n).bit (shiftedRowIndex offset i))

/-- Numerator source wires are disjoint from all shifted product-row targets. -/
theorem productRowWorkspaceNumerator_ne_shiftedRow_of_bits
    (n : Nat) (offset sourceBit targetBit : Fin n) :
    ((productRowWorkspaceNumeratorWord n).bit sourceBit).wire ≠
      ((productRowWorkspaceShiftedRowWord n offset).bit targetBit).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit sourceBit)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit (shiftedRowIndex offset targetBit))).wire
  exact
    productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
      ((productNumeratorWord n).bit sourceBit)
      ((productRowWord n).bit (shiftedRowIndex offset targetBit))

/-- Numerator source wires are disjoint from any product-row target bit. -/
theorem productRowWorkspaceNumerator_ne_rowBit
    (n : Nat) (sourceBit targetBit : Fin n) :
    ((productRowWorkspaceNumeratorWord n).bit sourceBit).wire ≠
      ((productRowWorkspaceRowWord n).bit targetBit).wire := by
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit sourceBit)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit targetBit)).wire
  exact
    productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
      ((productNumeratorWord n).bit sourceBit)
      ((productRowWord n).bit targetBit)

/-- Inverse-scratch controls are disjoint from every truncated shifted target
used by the filtered product-row load. -/
theorem productRowWorkspaceInverseScratch_ne_truncatedShiftedRow
    (n : Nat) (offset bit : Fin n) :
    ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
      ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit bit).wire := by
  unfold productRowWorkspaceTruncatedShiftedRowWord
  by_cases h : bit.val + offset.val < n
  · simpa [h] using
      productRowWorkspaceInverseScratch_ne_rowBit n offset
        (truncatedShiftedRowIndex offset bit h)
  · simpa [h] using
      productRowWorkspaceInverseScratch_ne_rowBit n offset bit

/-- Numerator sources are disjoint from every truncated shifted target used by
the filtered product-row load. -/
theorem productRowWorkspaceNumerator_ne_truncatedShiftedRow
    (n : Nat) (sourceBit offset targetBit : Fin n) :
    ((productRowWorkspaceNumeratorWord n).bit sourceBit).wire ≠
      ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit targetBit).wire := by
  unfold productRowWorkspaceTruncatedShiftedRowWord
  by_cases h : targetBit.val + offset.val < n
  · simpa [h] using
      productRowWorkspaceNumerator_ne_rowBit n sourceBit
        (truncatedShiftedRowIndex offset targetBit h)
  · simpa [h] using
      productRowWorkspaceNumerator_ne_rowBit n sourceBit targetBit

/-- Truncated shifted targets are wire-disjoint for distinct selected source
bits. -/
theorem productRowWorkspaceTruncatedShiftedRow_ne_of_mem_ne
    (n : Nat) (offset : Fin n) {i j : Fin n}
    (hi : i ∈ truncatedShiftedRowSources n offset)
    (hj : j ∈ truncatedShiftedRowSources n offset)
    (hij : i ≠ j) :
    ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit i).wire ≠
      ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit j).wire := by
  have hiValid := (mem_truncatedShiftedRowSources n offset i).mp hi
  have hjValid := (mem_truncatedShiftedRowSources n offset j).mp hj
  have hidx :
      truncatedShiftedRowIndex offset i hiValid ≠
        truncatedShiftedRowIndex offset j hjValid := by
    intro h
    exact hij (truncatedShiftedRowIndex_injective offset hiValid hjValid h)
  unfold productRowWorkspaceTruncatedShiftedRowWord
  dsimp
  rw [dif_pos hiValid, dif_pos hjValid]
  change
    (productWorkspaceBit n (productRowEncoding n)
      ((productRowWord n).bit
        (truncatedShiftedRowIndex offset i hiValid))).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit
          (truncatedShiftedRowIndex offset j hjValid))).wire
  exact
    productWorkspaceBit_ne_of_ne n (productRowEncoding n)
      ((productRowWord n).bit (truncatedShiftedRowIndex offset i hiValid))
      ((productRowWord n).bit (truncatedShiftedRowIndex offset j hjValid))
      (productRowBit_ne n hidx)

/-- Distinct shifted product-row targets occupy distinct wires. -/
theorem productRowWorkspaceShiftedRow_ne_of_ne
    (n : Nat) (offset : Fin n) {i j : Fin n} (hij : i ≠ j) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).wire ≠
      ((productRowWorkspaceShiftedRowWord n offset).bit j).wire := by
  change
    (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit (shiftedRowIndex offset i))).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit (shiftedRowIndex offset j))).wire
  exact
    productWorkspaceBit_ne_of_ne n (productRowEncoding n)
      ((productRowWord n).bit (shiftedRowIndex offset i))
      ((productRowWord n).bit (shiftedRowIndex offset j))
      (productRowBit_ne n (shiftedRowIndex_ne offset hij))

/-- One non-wrapping shifted partial-product Toffoli gate. -/
def productRowTruncatedShiftedLoadGate (n : Nat) (offset bit : Fin n)
    (h : bit.val + offset.val < n) :
    EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n) :=
  EncodedBit.GateSpec.toffoli
    ((productRowWorkspaceInverseScratchWord n).bit offset)
    ((productRowWorkspaceNumeratorWord n).bit bit)
    ((productRowWorkspaceRowWord n).bit
      (truncatedShiftedRowIndex offset bit h))
    (productRowWorkspaceInverseScratch_ne_numerator n offset bit)
    (productRowWorkspaceInverseScratch_ne_rowBit n offset
      (truncatedShiftedRowIndex offset bit h))
    (productRowWorkspaceNumerator_ne_rowBit n bit
      (truncatedShiftedRowIndex offset bit h))

/-- One indexed Toffoli gate from the filtered source list.  The target word is
defined for all indices, but only indices in `truncatedShiftedRowSources` are
executed by the surrounding gate list. -/
def productRowTruncatedShiftedLoadIndexGate (n : Nat) (offset bit : Fin n) :
    EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n) :=
  EncodedBit.GateSpec.toffoli
    ((productRowWorkspaceInverseScratchWord n).bit offset)
    ((productRowWorkspaceNumeratorWord n).bit bit)
    ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit bit)
    (productRowWorkspaceInverseScratch_ne_numerator n offset bit)
    (productRowWorkspaceInverseScratch_ne_truncatedShiftedRow n offset bit)
    (productRowWorkspaceNumerator_ne_truncatedShiftedRow n bit offset bit)

/-- Filtered Toffoli gate list for loading one low-bit shifted partial-product
row. Source bits whose shift would overflow the low `n` output bits are omitted,
matching multiplication in `ZMod (2^n)` rather than a cyclic convolution
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
def productRowTruncatedShiftedLoadGates (n : Nat) (offset : Fin n) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  (truncatedShiftedRowSources n offset).map
    (productRowTruncatedShiftedLoadIndexGate n offset)

/-- Base-gate program for one non-wrapping shifted product-row load. -/
def productRowTruncatedShiftedLoadProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  EncodedBit.GateSpec.programList
    (productRowTruncatedShiftedLoadGates n offset)

/-- Folded semantic action for one non-wrapping shifted product-row load. -/
def productRowTruncatedShiftedLoadStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  EncodedBit.GateSpec.stepList
    (productRowTruncatedShiftedLoadGates n offset)

/-- The non-wrapping shifted product-row load realizes its folded Toffoli
semantics on the same filtered gate object. -/
theorem productRowTruncatedShiftedLoad_realizes
    (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowTruncatedShiftedLoadProgram n offset)
      (productRowTruncatedShiftedLoadStep n offset) :=
  EncodedBit.GateSpec.realizesList
    (productRowTruncatedShiftedLoadGates n offset)

/-- A non-wrapping shifted product-row load preserves the denominator. -/
theorem productRowTruncatedShiftedLoadStep_get_denominator
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedShiftedLoadStep n offset x).1.1.denominator =
      x.1.1.denominator := by
  unfold productRowTruncatedShiftedLoadStep
  exact EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun y : PipelineWithProductRowWork n => y.1.1.denominator)
    (gates := productRowTruncatedShiftedLoadGates n offset)
    (by
      intro gate hgate
      rcases List.mem_map.mp
          (by simpa [productRowTruncatedShiftedLoadGates] using hgate) with
        ⟨bit, _hbit, rfl⟩
      simp [productRowTruncatedShiftedLoadIndexGate,
        EncodedBit.GateSpec.targetFlipPreserves])
    x

/-- The filtered gate-list step is the indexed controlled-xor fold over exactly
the non-overflowing source indices. -/
theorem productRowTruncatedShiftedLoadStep_eq_indicesStep
    (n : Nat) (offset : Fin n) :
    productRowTruncatedShiftedLoadStep n offset =
      EncodedBit.Word.controlledXorIntoIndicesStep
        ((productRowWorkspaceInverseScratchWord n).bit offset)
        (productRowWorkspaceNumeratorWord n)
        (productRowWorkspaceTruncatedShiftedRowWord n offset)
        (truncatedShiftedRowSources n offset) := by
  funext x
  unfold productRowTruncatedShiftedLoadStep
    productRowTruncatedShiftedLoadGates
    productRowTruncatedShiftedLoadIndexGate
    EncodedBit.Word.controlledXorIntoIndicesStep
  rw [EncodedBit.GateSpec.stepList_eq_foldl]
  generalize truncatedShiftedRowSources n offset = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [EncodedBit.GateSpec.step] using
        ih (((productRowWorkspaceInverseScratchWord n).bit offset).toffoliStep
          ((productRowWorkspaceNumeratorWord n).bit bit)
          ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit bit)
          x)

/-- A non-wrapping shifted product-row load preserves any observed readout
disjoint from all product-row target bits. -/
theorem productRowTruncatedShiftedLoadStep_get_observed_of_row_ne
    (n : Nat) (offset : Fin n)
    (observed : EncodedBit (pipelineWithProductRowWorkEncoding n))
    (hne :
      ∀ target : Fin n,
        ((productRowWorkspaceRowWord n).bit target).wire ≠ observed.wire)
    (x : PipelineWithProductRowWork n) :
    observed.get (productRowTruncatedShiftedLoadStep n offset x) =
      observed.get x := by
  rw [productRowTruncatedShiftedLoadStep_eq_indicesStep]
  exact
    EncodedBit.Word.controlledXorIntoIndicesStep_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset)
      observed
      (fun bit _ => by
        unfold productRowWorkspaceTruncatedShiftedRowWord
        by_cases h : bit.val + offset.val < n
        · simpa [h] using hne (truncatedShiftedRowIndex offset bit h)
        · simpa [h] using hne bit)
      x

/-- A non-wrapping shifted product-row load toggles exactly the selected
low-output target bit by the corresponding controlled numerator bit. -/
theorem productRowTruncatedShiftedLoadStep_get_truncatedRowBit
    (n : Nat) (offset bit : Fin n)
    (h : bit.val + offset.val < n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit
        (truncatedShiftedRowIndex offset bit h)).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      (((productRowWorkspaceRowWord n).bit
          (truncatedShiftedRowIndex offset bit h)).get x ^^
        (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
          ((productRowWorkspaceNumeratorWord n).bit bit).get x)) := by
  have hmem : bit ∈ truncatedShiftedRowSources n offset :=
    (mem_truncatedShiftedRowSources n offset bit).mpr h
  rw [productRowTruncatedShiftedLoadStep_eq_indicesStep]
  have htarget :=
    EncodedBit.Word.controlledXorIntoIndicesStep_get_target_of_mem
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset)
      (truncatedShiftedRowSources_nodup n offset)
      bit
      (fun j hj hji =>
        productRowWorkspaceTruncatedShiftedRow_ne_of_mem_ne
          n offset hj hmem hji)
      (fun j hj => by
        have hjValid := (mem_truncatedShiftedRowSources n offset j).mp hj
        simpa [productRowWorkspaceTruncatedShiftedRowWord, hjValid] using
          Ne.symm
            (productRowWorkspaceInverseScratch_ne_rowBit n offset
              (truncatedShiftedRowIndex offset j hjValid)))
      (fun j hj => by
        have hjValid := (mem_truncatedShiftedRowSources n offset j).mp hj
        simpa [productRowWorkspaceTruncatedShiftedRowWord, hjValid] using
          Ne.symm
            (productRowWorkspaceNumerator_ne_rowBit n bit
              (truncatedShiftedRowIndex offset j hjValid)))
      x
  simpa [productRowWorkspaceTruncatedShiftedRowWord, h, hmem] using htarget

/-- A non-wrapping shifted product-row load preserves row bits that are not
selected as low-output targets by the filtered source list. -/
theorem productRowTruncatedShiftedLoadStep_get_rowBit_of_target_ne
    (n : Nat) (offset target : Fin n)
    (hne :
      ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h ≠ target)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit target).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      ((productRowWorkspaceRowWord n).bit target).get x := by
  rw [productRowTruncatedShiftedLoadStep_eq_indicesStep]
  exact
    EncodedBit.Word.controlledXorIntoIndicesStep_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset)
      ((productRowWorkspaceRowWord n).bit target)
      (fun bit hmem => by
        have hvalid :=
          (mem_truncatedShiftedRowSources n offset bit).mp hmem
        unfold productRowWorkspaceTruncatedShiftedRowWord
        dsimp
        rw [dif_pos hvalid]
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit
              (truncatedShiftedRowIndex offset bit hvalid))).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit target)).wire
        exact
          productWorkspaceBit_ne_of_ne n (productRowEncoding n)
            ((productRowWord n).bit
              (truncatedShiftedRowIndex offset bit hvalid))
            ((productRowWord n).bit target)
            (productRowBit_ne n (hne bit hvalid)))
      x

/-- The non-wrapping row loaded from the source pipeline when the product row
starts clean. -/
def productRowTruncatedCleanLoadedRow
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    ProductRowWork n :=
  (productRowTruncatedShiftedLoadStep n offset (x.1, 0)).2

/-- If the product row is already clean, the filtered load produces the clean
loaded-row value. -/
theorem productRowTruncatedShiftedLoadStep_get_row_clean
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowTruncatedShiftedLoadStep n offset x).2 =
      productRowTruncatedCleanLoadedRow n offset x := by
  have hx : (x.1, (0 : ProductRowWork n)) = x := by
    cases x with
    | mk pipeline row =>
        simp at hrow
        simp [hrow]
  rw [← hx]
  rfl

/-- Bit formula for the non-wrapping clean loaded-row value at a selected
low-output target bit. -/
theorem productRowTruncatedCleanLoadedRow_get_truncatedBit
    (n : Nat) (offset bit : Fin n)
    (h : bit.val + offset.val < n)
    (x : PipelineWithProductRowWork n) :
    (productRowTruncatedCleanLoadedRow n offset x).val.testBit
        (truncatedShiftedRowIndex offset bit h).val =
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit bit).get x) := by
  unfold productRowTruncatedCleanLoadedRow
  rw [← productRowWorkspaceRowBit_get_testBit n
    (truncatedShiftedRowIndex offset bit h)
    (productRowTruncatedShiftedLoadStep n offset
      (x.1, (0 : ProductRowWork n)))]
  rw [productRowTruncatedShiftedLoadStep_get_truncatedRowBit]
  have hrowBit :
      ((productRowWorkspaceRowWord n).bit
          (truncatedShiftedRowIndex offset bit h)).get
          (x.1, (0 : ProductRowWork n)) = false := by
    simp [productRowWorkspaceRowBit_get_testBit]
  have hinv :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get
          (x.1, (0 : ProductRowWork n)) =
        ((productRowWorkspaceInverseScratchWord n).bit offset).get x := by
    cases x
    rfl
  have hnum :
      ((productRowWorkspaceNumeratorWord n).bit bit).get
          (x.1, (0 : ProductRowWork n)) =
        ((productRowWorkspaceNumeratorWord n).bit bit).get x := by
    cases x
    rfl
  rw [hrowBit, hinv, hnum]
  simp

/-- Non-target bits of a non-wrapping clean loaded row remain zero. -/
theorem productRowTruncatedCleanLoadedRow_get_rowBit_of_target_ne
    (n : Nat) (offset target : Fin n)
    (hne :
      ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h ≠ target)
    (x : PipelineWithProductRowWork n) :
    (productRowTruncatedCleanLoadedRow n offset x).val.testBit target.val =
      false := by
  unfold productRowTruncatedCleanLoadedRow
  rw [← productRowWorkspaceRowBit_get_testBit n target
    (productRowTruncatedShiftedLoadStep n offset
      (x.1, (0 : ProductRowWork n)))]
  rw [productRowTruncatedShiftedLoadStep_get_rowBit_of_target_ne
    n offset target hne]
  simp [productRowWorkspaceRowBit_get_testBit]

/-- If the controlling inverse-scratch bit is false, the non-wrapping clean
loaded row is zero. -/
theorem productRowTruncatedCleanLoadedRow_eq_zero_of_inverseScratch_false
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hcontrol :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get x = false) :
    productRowTruncatedCleanLoadedRow n offset x = 0 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro target
  by_cases htarget :
      ∃ bit : Fin n, ∃ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h = target
  · rcases htarget with ⟨bit, h, hidx⟩
    rw [← hidx]
    rw [productRowTruncatedCleanLoadedRow_get_truncatedBit]
    rw [hcontrol]
    simp
  · have hne :
        ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
          truncatedShiftedRowIndex offset bit h ≠ target := by
      intro bit h hidx
      exact htarget ⟨bit, h, hidx⟩
    rw [productRowTruncatedCleanLoadedRow_get_rowBit_of_target_ne
      n offset target hne]
    simp

/-- If the controlling inverse-scratch bit is true, the non-wrapping clean
loaded row is the numerator shifted left by that offset, viewed in the low
`n` output bits. -/
theorem productRowTruncatedCleanLoadedRow_eq_shiftedNumerator_of_inverseScratch_true
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hcontrol :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get x = true) :
    productRowTruncatedCleanLoadedRow n offset x =
      ((x.1.1.numerator.val * 2 ^ offset.val : Nat) : ProductRowWork n) := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro target
  by_cases htarget :
      ∃ bit : Fin n, ∃ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h = target
  · rcases htarget with ⟨bit, h, hidx⟩
    rw [← hidx]
    rw [productRowTruncatedCleanLoadedRow_get_truncatedBit]
    rw [hcontrol]
    rw [zmod_twoPow_natCast_shifted_val_testBit]
    have hge : bit.val + offset.val ≥ offset.val := by omega
    have hsub : bit.val + offset.val - offset.val = bit.val := by omega
    simp [truncatedShiftedRowIndex, hge, hsub]
  · have hne :
        ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
          truncatedShiftedRowIndex offset bit h ≠ target := by
      intro bit h hidx
      exact htarget ⟨bit, h, hidx⟩
    rw [productRowTruncatedCleanLoadedRow_get_rowBit_of_target_ne
      n offset target hne]
    rw [zmod_twoPow_natCast_shifted_val_testBit]
    by_cases hge : target.val ≥ offset.val
    · by_cases hnum :
          x.1.1.numerator.val.testBit (target.val - offset.val)
      · have hbitLt : target.val - offset.val < n := by omega
        let bit : Fin n := ⟨target.val - offset.val, hbitLt⟩
        have hvalid : bit.val + offset.val < n := by
          dsimp [bit]
          omega
        have hidx : truncatedShiftedRowIndex offset bit hvalid = target := by
          apply Fin.ext
          dsimp [bit, truncatedShiftedRowIndex]
          omega
        exact False.elim (htarget ⟨bit, hvalid, hidx⟩)
      · simp [hge, hnum]
    · simp [hge]

/-- Closed form for one non-wrapping clean loaded row, controlled by the
corresponding inverse-scratch bit. -/
theorem productRowTruncatedCleanLoadedRow_eq_if_shiftedNumerator
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    productRowTruncatedCleanLoadedRow n offset x =
      if x.1.1.inverseScratch.val.testBit offset.val then
        ((x.1.1.numerator.val * 2 ^ offset.val : Nat) : ProductRowWork n)
      else
        0 := by
  by_cases hcontrol :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get x = true
  · have hbit : x.1.1.inverseScratch.val.testBit offset.val = true := by
      simpa using hcontrol
    rw [productRowTruncatedCleanLoadedRow_eq_shiftedNumerator_of_inverseScratch_true
      n offset x hcontrol]
    simp [hbit]
  · have hfalse :
        ((productRowWorkspaceInverseScratchWord n).bit offset).get x = false := by
      exact Bool.eq_false_iff.mpr hcontrol
    have hbit : x.1.1.inverseScratch.val.testBit offset.val = false := by
      simpa using hfalse
    rw [productRowTruncatedCleanLoadedRow_eq_zero_of_inverseScratch_false
      n offset x hfalse]
    simp [hbit]

/-- A non-wrapping shifted product-row load writes only the trailing row
workspace; every pipeline-register readout is preserved. -/
theorem productRowTruncatedShiftedLoadStep_get_pipelineBit
    (n : Nat) (offset : Fin n)
    (bit : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (x : PipelineWithProductRowWork n) :
    (productWorkspacePipelineBit n (productRowEncoding n) bit).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n) bit).get x := by
  exact
    productRowTruncatedShiftedLoadStep_get_observed_of_row_ne
      n offset (productWorkspacePipelineBit n (productRowEncoding n) bit)
      (fun target => by
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit target)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n) bit).wire
        exact
          Ne.symm
            (productWorkspacePipelineBit_ne_productBit n
              (productRowEncoding n) bit ((productRowWord n).bit target)))
      x

/-- A non-wrapping shifted product-row load preserves the quotient-scratch
word. -/
theorem productRowTruncatedShiftedLoadStep_get_quotientScratch
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedShiftedLoadStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceQuotientScratchBit_get_testBit n bit
      (productRowTruncatedShiftedLoadStep n offset x)]
  have hbit :
      ((productRowWorkspaceQuotientScratchWord n).bit bit).get
          (productRowTruncatedShiftedLoadStep n offset x) =
        ((productRowWorkspaceQuotientScratchWord n).bit bit).get x := by
    simpa [productRowWorkspaceQuotientScratchWord,
      productWorkspaceQuotientScratchWord, productWorkspacePipelineWord] using
      productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
        ((productQuotientScratchWord n).bit bit) x
  rw [hbit]
  exact productRowWorkspaceQuotientScratchBit_get_testBit n bit x

/-- A non-wrapping shifted product-row load preserves an inverse-scratch
readout. -/
theorem productRowTruncatedShiftedLoadStep_get_inverseScratchBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      ((productRowWorkspaceInverseScratchWord n).bit i).get x := by
  simpa [productRowWorkspaceInverseScratchWord,
    productWorkspaceInverseScratchWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
      ((productInverseScratchWord n).bit i) x

/-- A non-wrapping shifted product-row load preserves a numerator readout. -/
theorem productRowTruncatedShiftedLoadStep_get_numeratorBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      ((productRowWorkspaceNumeratorWord n).bit i).get x := by
  simpa [productRowWorkspaceNumeratorWord,
    productWorkspaceNumeratorWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
      ((productNumeratorWord n).bit i) x

/-- A non-wrapping shifted product-row load preserves a target readout. -/
theorem productRowTruncatedShiftedLoadStep_get_targetBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit i).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      ((productRowWorkspaceTargetWord n).bit i).get x := by
  simpa [productRowWorkspaceTargetWord,
    productWorkspaceTargetWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
      ((productTargetWord n).bit i) x

/-- A non-wrapping shifted product-row load preserves the cleanup flag. -/
theorem productRowTruncatedShiftedLoadStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  simpa [productRowWorkspaceFlagBit, productWorkspaceFlagBit] using
    productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
      (productFlagBit n) x

/-- A non-wrapping shifted product-row load preserves each temporary carry-work
bit. -/
theorem productRowTruncatedShiftedLoadStep_get_carryWorkBit
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowTruncatedShiftedLoadStep n offset x) =
      ((productRowWorkspaceCarryWorkWord n).bit j).get x := by
  simpa [productRowWorkspaceCarryWorkWord, productWorkspaceCarryWorkWord,
    productWorkspacePipelineWord] using
    productRowTruncatedShiftedLoadStep_get_pipelineBit n offset
      ((productCarryWorkWord n).bit j) x

/-- Same-Circuit witness for one non-wrapping shifted product-row load. -/
def productRowTruncatedShiftedLoadSameCircuit
    (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowTruncatedShiftedLoadStep n offset) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowTruncatedShiftedLoadProgram n offset
  realizes := productRowTruncatedShiftedLoad_realizes n offset

/-! #### Non-wrapping product-row unload -/

/-- Reverse filtered Toffoli list for unloading one low-bit shifted
partial-product row. -/
def productRowTruncatedShiftedUnloadGates (n : Nat) (offset : Fin n) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  (productRowTruncatedShiftedLoadGates n offset).reverse

/-- Base-gate program for unloading one non-wrapping shifted product row. -/
def productRowTruncatedShiftedUnloadProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  EncodedBit.GateSpec.programList
    (productRowTruncatedShiftedUnloadGates n offset)

/-- Folded semantic action for unloading one non-wrapping shifted product row. -/
def productRowTruncatedShiftedUnloadStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  EncodedBit.GateSpec.stepList
    (productRowTruncatedShiftedUnloadGates n offset)

/-- The filtered unload realizes the reverse filtered gate object. -/
theorem productRowTruncatedShiftedUnload_realizes
    (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowTruncatedShiftedUnloadProgram n offset)
      (productRowTruncatedShiftedUnloadStep n offset) :=
  EncodedBit.GateSpec.realizesList
    (productRowTruncatedShiftedUnloadGates n offset)

/-- A non-wrapping shifted product-row unload preserves the denominator. -/
theorem productRowTruncatedShiftedUnloadStep_get_denominator
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedShiftedUnloadStep n offset x).1.1.denominator =
      x.1.1.denominator := by
  unfold productRowTruncatedShiftedUnloadStep
  exact EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun y : PipelineWithProductRowWork n => y.1.1.denominator)
    (gates := productRowTruncatedShiftedUnloadGates n offset)
    (by
      intro gate hgate
      have hload : gate ∈ productRowTruncatedShiftedLoadGates n offset := by
        simpa [productRowTruncatedShiftedUnloadGates] using
          List.mem_reverse.mp hgate
      rcases List.mem_map.mp
          (by simpa [productRowTruncatedShiftedLoadGates] using hload) with
        ⟨bit, _hbit, rfl⟩
      simp [productRowTruncatedShiftedLoadIndexGate,
        EncodedBit.GateSpec.targetFlipPreserves])
    x

/-- The reverse filtered unload step is the indexed controlled-xor fold over
the reversed non-overflowing source list. -/
theorem productRowTruncatedShiftedUnloadStep_eq_indicesStep
    (n : Nat) (offset : Fin n) :
    productRowTruncatedShiftedUnloadStep n offset =
      EncodedBit.Word.controlledXorIntoIndicesStep
        ((productRowWorkspaceInverseScratchWord n).bit offset)
        (productRowWorkspaceNumeratorWord n)
        (productRowWorkspaceTruncatedShiftedRowWord n offset)
        (truncatedShiftedRowSources n offset).reverse := by
  funext x
  unfold productRowTruncatedShiftedUnloadStep
    productRowTruncatedShiftedUnloadGates
    productRowTruncatedShiftedLoadGates
    productRowTruncatedShiftedLoadIndexGate
    EncodedBit.Word.controlledXorIntoIndicesStep
  rw [EncodedBit.GateSpec.stepList_eq_foldl]
  rw [← List.map_reverse]
  generalize (truncatedShiftedRowSources n offset).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [EncodedBit.GateSpec.step] using
        ih (((productRowWorkspaceInverseScratchWord n).bit offset).toffoliStep
          ((productRowWorkspaceNumeratorWord n).bit bit)
          ((productRowWorkspaceTruncatedShiftedRowWord n offset).bit bit)
          x)

/-- A non-wrapping shifted product-row unload preserves any observed readout
disjoint from all product-row target bits. -/
theorem productRowTruncatedShiftedUnloadStep_get_observed_of_row_ne
    (n : Nat) (offset : Fin n)
    (observed : EncodedBit (pipelineWithProductRowWorkEncoding n))
    (hne :
      ∀ target : Fin n,
        ((productRowWorkspaceRowWord n).bit target).wire ≠ observed.wire)
    (x : PipelineWithProductRowWork n) :
    observed.get (productRowTruncatedShiftedUnloadStep n offset x) =
      observed.get x := by
  rw [productRowTruncatedShiftedUnloadStep_eq_indicesStep]
  exact
    EncodedBit.Word.controlledXorIntoIndicesStep_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset).reverse
      observed
      (fun bit _ => by
        unfold productRowWorkspaceTruncatedShiftedRowWord
        by_cases h : bit.val + offset.val < n
        · simpa [h] using hne (truncatedShiftedRowIndex offset bit h)
        · simpa [h] using hne bit)
      x

/-- A non-wrapping shifted product-row unload writes only the trailing row
workspace; every pipeline-register readout is preserved. -/
theorem productRowTruncatedShiftedUnloadStep_get_pipelineBit
    (n : Nat) (offset : Fin n)
    (bit : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (x : PipelineWithProductRowWork n) :
    (productWorkspacePipelineBit n (productRowEncoding n) bit).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n) bit).get x := by
  exact
    productRowTruncatedShiftedUnloadStep_get_observed_of_row_ne
      n offset (productWorkspacePipelineBit n (productRowEncoding n) bit)
      (fun target => by
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit target)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n) bit).wire
        exact
          Ne.symm
            (productWorkspacePipelineBit_ne_productBit n
              (productRowEncoding n) bit ((productRowWord n).bit target)))
      x

/-- A non-wrapping shifted product-row unload preserves the quotient-scratch
word. -/
theorem productRowTruncatedShiftedUnloadStep_get_quotientScratch
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedShiftedUnloadStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceQuotientScratchBit_get_testBit n bit
      (productRowTruncatedShiftedUnloadStep n offset x)]
  have hbit :
      ((productRowWorkspaceQuotientScratchWord n).bit bit).get
          (productRowTruncatedShiftedUnloadStep n offset x) =
        ((productRowWorkspaceQuotientScratchWord n).bit bit).get x := by
    simpa [productRowWorkspaceQuotientScratchWord,
      productWorkspaceQuotientScratchWord, productWorkspacePipelineWord] using
      productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
        ((productQuotientScratchWord n).bit bit) x
  rw [hbit]
  exact productRowWorkspaceQuotientScratchBit_get_testBit n bit x

/-- A non-wrapping shifted product-row unload preserves an inverse-scratch
readout. -/
theorem productRowTruncatedShiftedUnloadStep_get_inverseScratchBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      ((productRowWorkspaceInverseScratchWord n).bit i).get x := by
  simpa [productRowWorkspaceInverseScratchWord,
    productWorkspaceInverseScratchWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
      ((productInverseScratchWord n).bit i) x

/-- A non-wrapping shifted product-row unload preserves a numerator readout. -/
theorem productRowTruncatedShiftedUnloadStep_get_numeratorBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      ((productRowWorkspaceNumeratorWord n).bit i).get x := by
  simpa [productRowWorkspaceNumeratorWord,
    productWorkspaceNumeratorWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
      ((productNumeratorWord n).bit i) x

/-- A non-wrapping shifted product-row unload preserves a target readout. -/
theorem productRowTruncatedShiftedUnloadStep_get_targetBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit i).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      ((productRowWorkspaceTargetWord n).bit i).get x := by
  simpa [productRowWorkspaceTargetWord,
    productWorkspaceTargetWord, productWorkspacePipelineWord] using
    productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
      ((productTargetWord n).bit i) x

/-- A non-wrapping shifted product-row unload preserves the cleanup flag. -/
theorem productRowTruncatedShiftedUnloadStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  simpa [productRowWorkspaceFlagBit, productWorkspaceFlagBit] using
    productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
      (productFlagBit n) x

/-- A non-wrapping shifted product-row unload preserves each temporary
carry-work bit. -/
theorem productRowTruncatedShiftedUnloadStep_get_carryWorkBit
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      ((productRowWorkspaceCarryWorkWord n).bit j).get x := by
  simpa [productRowWorkspaceCarryWorkWord, productWorkspaceCarryWorkWord,
    productWorkspacePipelineWord] using
    productRowTruncatedShiftedUnloadStep_get_pipelineBit n offset
      ((productCarryWorkWord n).bit j) x

/-- A non-wrapping shifted product-row unload toggles exactly the selected
low-output target bit by the corresponding controlled numerator bit. -/
theorem productRowTruncatedShiftedUnloadStep_get_truncatedRowBit
    (n : Nat) (offset bit : Fin n)
    (h : bit.val + offset.val < n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit
        (truncatedShiftedRowIndex offset bit h)).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      (((productRowWorkspaceRowWord n).bit
          (truncatedShiftedRowIndex offset bit h)).get x ^^
        (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
          ((productRowWorkspaceNumeratorWord n).bit bit).get x)) := by
  have hmem : bit ∈ (truncatedShiftedRowSources n offset).reverse := by
    simp [(mem_truncatedShiftedRowSources n offset bit).mpr h]
  rw [productRowTruncatedShiftedUnloadStep_eq_indicesStep]
  have htarget :=
    EncodedBit.Word.controlledXorIntoIndicesStep_get_target_of_mem
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset).reverse
      (List.nodup_reverse.mpr (truncatedShiftedRowSources_nodup n offset))
      bit
      (fun j hj hji =>
        productRowWorkspaceTruncatedShiftedRow_ne_of_mem_ne
          n offset (by simpa using List.mem_reverse.mp hj)
          ((mem_truncatedShiftedRowSources n offset bit).mpr h) hji)
      (fun j hj => by
        have hjSource : j ∈ truncatedShiftedRowSources n offset := by
          simpa using List.mem_reverse.mp hj
        have hjValid := (mem_truncatedShiftedRowSources n offset j).mp hjSource
        simpa [productRowWorkspaceTruncatedShiftedRowWord, hjValid] using
          Ne.symm
            (productRowWorkspaceInverseScratch_ne_rowBit n offset
              (truncatedShiftedRowIndex offset j hjValid)))
      (fun j hj => by
        have hjSource : j ∈ truncatedShiftedRowSources n offset := by
          simpa using List.mem_reverse.mp hj
        have hjValid := (mem_truncatedShiftedRowSources n offset j).mp hjSource
        simpa [productRowWorkspaceTruncatedShiftedRowWord, hjValid] using
          Ne.symm
            (productRowWorkspaceNumerator_ne_rowBit n bit
              (truncatedShiftedRowIndex offset j hjValid)))
      x
  simpa [productRowWorkspaceTruncatedShiftedRowWord, h, hmem] using htarget

/-- A non-wrapping shifted product-row unload preserves row bits that are not
selected as low-output targets by the filtered source list. -/
theorem productRowTruncatedShiftedUnloadStep_get_rowBit_of_target_ne
    (n : Nat) (offset target : Fin n)
    (hne :
      ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h ≠ target)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit target).get
        (productRowTruncatedShiftedUnloadStep n offset x) =
      ((productRowWorkspaceRowWord n).bit target).get x := by
  rw [productRowTruncatedShiftedUnloadStep_eq_indicesStep]
  exact
    EncodedBit.Word.controlledXorIntoIndicesStep_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceTruncatedShiftedRowWord n offset)
      (truncatedShiftedRowSources n offset).reverse
      ((productRowWorkspaceRowWord n).bit target)
      (fun bit hmem => by
        have hsource : bit ∈ truncatedShiftedRowSources n offset := by
          simpa using List.mem_reverse.mp hmem
        have hvalid :=
          (mem_truncatedShiftedRowSources n offset bit).mp hsource
        unfold productRowWorkspaceTruncatedShiftedRowWord
        dsimp
        rw [dif_pos hvalid]
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit
              (truncatedShiftedRowIndex offset bit hvalid))).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit target)).wire
        exact
          productWorkspaceBit_ne_of_ne n (productRowEncoding n)
            ((productRowWord n).bit
              (truncatedShiftedRowIndex offset bit hvalid))
            ((productRowWord n).bit target)
            (productRowBit_ne n (hne bit hvalid)))
      x

/-- Same-Circuit witness for one non-wrapping shifted product-row unload. -/
def productRowTruncatedShiftedUnloadSameCircuit
    (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowTruncatedShiftedUnloadStep n offset) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowTruncatedShiftedUnloadProgram n offset
  realizes := productRowTruncatedShiftedUnload_realizes n offset

/-- Toffoli gate list for loading one shifted partial-product row:
`row[i + offset] ^= inverseScratch[offset] && numerator[i]`.
The disjointness hypotheses record the remaining concrete wire-layout
obligations for this product-row route [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350]. -/
def controlledShiftedRowLoadGates (n : Nat) (offset : Fin n)
    (hcontrolSource :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceNumeratorWord n).bit i).wire)
    (hcontrolTarget :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire)
    (hsourceTarget :
      ∀ i,
        ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  EncodedBit.Word.controlledXorIntoGates
    ((productRowWorkspaceInverseScratchWord n).bit offset)
    (productRowWorkspaceNumeratorWord n)
    (productRowWorkspaceShiftedRowWord n offset)
    hcontrolSource hcontrolTarget hsourceTarget

/-- Base-gate program for one controlled shifted product-row load. -/
def controlledShiftedRowLoadProgram (n : Nat) (offset : Fin n)
    (hcontrolSource :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceNumeratorWord n).bit i).wire)
    (hcontrolTarget :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire)
    (hsourceTarget :
      ∀ i,
        ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  EncodedBit.GateSpec.programList
    (controlledShiftedRowLoadGates n offset
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Folded semantic action for one controlled shifted product-row load. -/
def controlledShiftedRowLoadStep (n : Nat) (offset : Fin n)
    (hcontrolSource :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceNumeratorWord n).bit i).wire)
    (hcontrolTarget :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire)
    (hsourceTarget :
      ∀ i,
        ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  EncodedBit.GateSpec.stepList
    (controlledShiftedRowLoadGates n offset
      hcontrolSource hcontrolTarget hsourceTarget)

/-- The controlled shifted row-load program realizes the folded Toffoli
semantics on the same encoded gate object. -/
theorem controlledShiftedRowLoad_realizes (n : Nat) (offset : Fin n)
    (hcontrolSource :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceNumeratorWord n).bit i).wire)
    (hcontrolTarget :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire)
    (hsourceTarget :
      ∀ i,
        ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (controlledShiftedRowLoadProgram n offset
        hcontrolSource hcontrolTarget hsourceTarget)
      (controlledShiftedRowLoadStep n offset
        hcontrolSource hcontrolTarget hsourceTarget) :=
  EncodedBit.GateSpec.realizesList
    (controlledShiftedRowLoadGates n offset
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Same-Circuit witness for one controlled shifted product-row load. -/
def controlledShiftedRowLoadSameCircuit (n : Nat) (offset : Fin n)
    (hcontrolSource :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceNumeratorWord n).bit i).wire)
    (hcontrolTarget :
      ∀ i,
        ((productRowWorkspaceInverseScratchWord n).bit offset).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire)
    (hsourceTarget :
      ∀ i,
        ((productRowWorkspaceNumeratorWord n).bit i).wire ≠
          ((productRowWorkspaceShiftedRowWord n offset).bit i).wire) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (controlledShiftedRowLoadStep n offset
        hcontrolSource hcontrolTarget hsourceTarget) where
  encoding := pipelineWithProductRowWorkEncoding n
  program :=
    controlledShiftedRowLoadProgram n offset
      hcontrolSource hcontrolTarget hsourceTarget
  realizes :=
    controlledShiftedRowLoad_realizes n offset
      hcontrolSource hcontrolTarget hsourceTarget

/-- Concrete Toffoli gate list for one shifted product-row load in the
selected one-row product workspace. -/
def productRowControlledShiftedLoadGates (n : Nat) (offset : Fin n) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  controlledShiftedRowLoadGates n offset
    (productRowWorkspaceInverseScratch_ne_numerator n offset)
    (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
    (productRowWorkspaceNumerator_ne_shiftedRow n offset)

/-- Concrete base-gate program for one shifted product-row load. -/
def productRowControlledShiftedLoadProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  controlledShiftedRowLoadProgram n offset
    (productRowWorkspaceInverseScratch_ne_numerator n offset)
    (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
    (productRowWorkspaceNumerator_ne_shiftedRow n offset)

/-- Concrete folded semantic action for one shifted product-row load. -/
def productRowControlledShiftedLoadStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  controlledShiftedRowLoadStep n offset
    (productRowWorkspaceInverseScratch_ne_numerator n offset)
    (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
    (productRowWorkspaceNumerator_ne_shiftedRow n offset)

/-- A shifted product-row load writes only the trailing row workspace; every
pipeline-register readout is preserved. -/
theorem productRowControlledShiftedLoadStep_get_pipelineBit
    (n : Nat) (offset : Fin n)
    (bit : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (x : PipelineWithProductRowWork n) :
    (productWorkspacePipelineBit n (productRowEncoding n) bit).get
        (productRowControlledShiftedLoadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n) bit).get x := by
  unfold productRowControlledShiftedLoadStep controlledShiftedRowLoadStep
  exact
    EncodedBit.Word.controlledXorIntoStep_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceShiftedRowWord n offset)
      (productRowWorkspaceInverseScratch_ne_numerator n offset)
      (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
      (productRowWorkspaceNumerator_ne_shiftedRow n offset)
      (productWorkspacePipelineBit n (productRowEncoding n) bit)
      (fun i => by
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit (shiftedRowIndex offset i))).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n) bit).wire
        exact
          Ne.symm
            (productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
              bit ((productRowWord n).bit (shiftedRowIndex offset i))))
      x

/-- A shifted product-row load preserves the quotient-scratch word. -/
theorem productRowControlledShiftedLoadStep_get_quotientScratch
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowControlledShiftedLoadStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceQuotientScratchBit_get_testBit n bit
      (productRowControlledShiftedLoadStep n offset x)]
  have hbit :
      ((productRowWorkspaceQuotientScratchWord n).bit bit).get
          (productRowControlledShiftedLoadStep n offset x) =
        ((productRowWorkspaceQuotientScratchWord n).bit bit).get x := by
    simpa [productRowWorkspaceQuotientScratchWord,
      productWorkspaceQuotientScratchWord, productWorkspacePipelineWord] using
      productRowControlledShiftedLoadStep_get_pipelineBit n offset
        ((productQuotientScratchWord n).bit bit) x
  rw [hbit]
  exact productRowWorkspaceQuotientScratchBit_get_testBit n bit x

/-- A shifted product-row load preserves the cleanup flag. -/
theorem productRowControlledShiftedLoadStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowControlledShiftedLoadStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  simpa [productRowWorkspaceFlagBit, productWorkspaceFlagBit] using
    productRowControlledShiftedLoadStep_get_pipelineBit n offset
      (productFlagBit n) x

/-- A shifted product-row load preserves each temporary carry-work bit. -/
theorem productRowControlledShiftedLoadStep_get_carryWorkBit
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowControlledShiftedLoadStep n offset x) =
      ((productRowWorkspaceCarryWorkWord n).bit j).get x := by
  simpa [productRowWorkspaceCarryWorkWord, productWorkspaceCarryWorkWord,
    productWorkspacePipelineWord] using
    productRowControlledShiftedLoadStep_get_pipelineBit n offset
      ((productCarryWorkWord n).bit j) x

/-- A shifted product-row load toggles each shifted row target by the
corresponding controlled numerator bit. -/
theorem productRowControlledShiftedLoadStep_get_shiftedRowBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowControlledShiftedLoadStep n offset x) =
      (((productRowWorkspaceShiftedRowWord n offset).bit i).get x ^^
        (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
          ((productRowWorkspaceNumeratorWord n).bit i).get x)) := by
  unfold productRowControlledShiftedLoadStep controlledShiftedRowLoadStep
  exact
    EncodedBit.Word.controlledXorIntoStep_get_target
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceShiftedRowWord n offset)
      (productRowWorkspaceInverseScratch_ne_numerator n offset)
      (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
      (productRowWorkspaceNumerator_ne_shiftedRow n offset)
      i
      (fun j hji => productRowWorkspaceShiftedRow_ne_of_ne n offset hji)
      (fun j => Ne.symm (productRowWorkspaceInverseScratch_ne_shiftedRow n offset j))
      (fun j =>
        Ne.symm
          (productRowWorkspaceNumerator_ne_shiftedRow_of_bits n offset i j))
      x

/-- Loading from a clean row writes exactly the selected shifted numerator bit. -/
theorem productRowControlledShiftedLoadStep_get_shiftedRowBit_clean
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowControlledShiftedLoadStep n offset x) =
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit i).get x) := by
  rw [productRowControlledShiftedLoadStep_get_shiftedRowBit]
  have hrowBit :
      ((productRowWorkspaceShiftedRowWord n offset).bit i).get x = false := by
    simp [productRowWorkspaceShiftedRowWord,
      productRowWorkspaceRowBit_get_testBit, hrow]
  rw [hrowBit]
  simp

/-- Clean-load row bits, read at the shifted physical row index. -/
theorem productRowControlledShiftedLoadStep_get_row_shiftedBit_clean
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowControlledShiftedLoadStep n offset x).2.val.testBit
        (shiftedRowIndex offset i).val =
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit i).get x) := by
  rw [← productRowWorkspaceRowBit_get_testBit n
    (shiftedRowIndex offset i) (productRowControlledShiftedLoadStep n offset x)]
  change
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowControlledShiftedLoadStep n offset x) =
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit i).get x)
  exact productRowControlledShiftedLoadStep_get_shiftedRowBit_clean
    n offset i x hrow

/-- The row loaded from the source pipeline when the product row starts clean. -/
def productRowCleanLoadedRow
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    ProductRowWork n :=
  (productRowControlledShiftedLoadStep n offset (x.1, 0)).2

/-- If the product row is already clean, the concrete load produces the clean
loaded-row value. -/
theorem productRowControlledShiftedLoadStep_get_row_clean
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowControlledShiftedLoadStep n offset x).2 =
      productRowCleanLoadedRow n offset x := by
  have hx : (x.1, (0 : ProductRowWork n)) = x := by
    cases x with
    | mk pipeline row =>
        simp at hrow
        simp [hrow]
  rw [← hx]
  rfl

/-- Bit formula for the clean loaded-row value at its shifted row index. -/
theorem productRowCleanLoadedRow_get_shiftedBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowCleanLoadedRow n offset x).val.testBit
        (shiftedRowIndex offset i).val =
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit i).get x) := by
  unfold productRowCleanLoadedRow
  have hload :=
    productRowControlledShiftedLoadStep_get_row_shiftedBit_clean
      n offset i (x.1, (0 : ProductRowWork n)) rfl
  have hinv :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get
          (x.1, (0 : ProductRowWork n)) =
        ((productRowWorkspaceInverseScratchWord n).bit offset).get x := by
    cases x
    rfl
  have hnum :
      ((productRowWorkspaceNumeratorWord n).bit i).get
          (x.1, (0 : ProductRowWork n)) =
        ((productRowWorkspaceNumeratorWord n).bit i).get x := by
    cases x
    rfl
  rwa [hinv, hnum] at hload

/-- The concrete shifted product-row load realizes its folded Toffoli
semantics on the same gate object. -/
theorem productRowControlledShiftedLoad_realizes (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowControlledShiftedLoadProgram n offset)
      (productRowControlledShiftedLoadStep n offset) :=
  controlledShiftedRowLoad_realizes n offset
    (productRowWorkspaceInverseScratch_ne_numerator n offset)
    (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
    (productRowWorkspaceNumerator_ne_shiftedRow n offset)

/-- Same-Circuit witness for one concrete shifted product-row load. -/
def productRowControlledShiftedLoadSameCircuit (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowControlledShiftedLoadStep n offset) :=
  controlledShiftedRowLoadSameCircuit n offset
    (productRowWorkspaceInverseScratch_ne_numerator n offset)
    (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
    (productRowWorkspaceNumerator_ne_shiftedRow n offset)

/-! #### Product-row adder layout -/

/-- Carry-work layout for adding the loaded product row into quotient scratch.
The data carry flag and VBE carry-work register are reused from the division
pipeline, so the adder remains a folded X/CNOT/Toffoli gate object tied to the
same resource accounting path [VBE95, 9511018.tex:237-264,591-618]. -/
def productRowAddCarryWorkLayout (n : Nat) :
    PlainAdder.Schedule.CarryWorkLayout
      (encoding := pipelineWithProductRowWorkEncoding n) n where
  left := productRowWorkspaceRowWord n
  right := productRowWorkspaceQuotientScratchWord n
  carryIn := productRowWorkspaceFlagBit n
  workCarry := productRowWorkspaceCarryWorkWord n
  leftLeft_ne := by
    intro i j hij
    change
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit i)).wire ≠
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit j)).wire
    exact
      productWorkspaceBit_ne_of_ne n (productRowEncoding n)
        ((productRowWord n).bit i) ((productRowWord n).bit j)
        (productRowBit_ne n hij)
  rightRight_ne := by
    intro i j hij
    change
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productQuotientScratchWord n).bit j)).wire
    exact
      productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i)
        ((productQuotientScratchWord n).bit j)
        (productQuotientScratchBit_ne n hij)
  leftRight_ne := by
    intro i j
    change
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productQuotientScratchWord n).bit j)).wire
    exact
      Ne.symm
        (productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
          ((productQuotientScratchWord n).bit j) ((productRowWord n).bit i))
  leftCarryIn_ne := by
    intro i
    change
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        (productFlagBit n)).wire
    exact
      Ne.symm
        (productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
          (productFlagBit n) ((productRowWord n).bit i))
  rightCarryIn_ne := by
    intro i
    change
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        (productFlagBit n)).wire
    exact
      productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i) (productFlagBit n)
        (productQuotientScratchBit_ne_flag n i)
  leftWork_ne := by
    intro i j
    change
      (productWorkspaceBit n (productRowEncoding n)
        ((productRowWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productCarryWorkWord n).bit j)).wire
    exact
      Ne.symm
        (productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
          ((productCarryWorkWord n).bit j) ((productRowWord n).bit i))
  rightWork_ne := by
    intro i j
    change
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productCarryWorkWord n).bit j)).wire
    exact
      productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
        ((productQuotientScratchWord n).bit i)
        ((productCarryWorkWord n).bit j)
        (productQuotientScratchBit_ne_carryWork n i j)
  carryInWork_ne := by
    intro j
    change
      (productWorkspacePipelineBit n (productRowEncoding n)
        (productFlagBit n)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productCarryWorkWord n).bit j)).wire
    exact
      productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
        (productFlagBit n) ((productCarryWorkWord n).bit j)
        (productFlagBit_ne_carryWork n j)
  workWork_ne := by
    intro i j hij
    change
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productCarryWorkWord n).bit i)).wire ≠
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productCarryWorkWord n).bit j)).wire
    exact
      productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
        ((productCarryWorkWord n).bit i)
        ((productCarryWorkWord n).bit j)
        (productCarryWorkBit_ne n hij)

/-- Folded carry/sum/cleanup gate list for adding a loaded product row into
quotient scratch. -/
def productRowAddGates (n : Nat) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
    (productRowAddCarryWorkLayout n)

/-- Base-gate program for adding a loaded product row into quotient scratch. -/
def productRowAddProgram (n : Nat) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
    (productRowAddCarryWorkLayout n)

/-- Folded semantic action for adding a loaded product row into quotient
scratch. -/
def productRowAddStep (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
    (productRowAddCarryWorkLayout n)

/-- Gate-list quotient-scratch bit formula for adding the loaded product row.
The carry term remains the concrete carry selected by the same folded
carry-work schedule; the clean-carry arithmetic invariant is proved separately. -/
theorem productRowAddStep_get_quotientScratchBit
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceQuotientScratchWord n).bit i).get
        (productRowAddStep n x) =
      ((((productRowWorkspaceQuotientScratchWord n).bit i).get x ^^
          ((productRowWorkspaceRowWord n).bit i).get x) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
          (productRowAddCarryWorkLayout n) i).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (productRowAddCarryWorkLayout n) x)) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (productRowAddCarryWorkLayout n) i x
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [productRowAddStep, productRowAddCarryWorkLayout,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using h

/-- Forward carry-work recurrence for the product-row adder layout on clean
flag/work inputs. -/
theorem productRowAddCarryStage_get_workCarry_natAddCarry
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (productRowAddCarryWorkLayout n) x) =
      PlainAdder.Schedule.PowerOfTwo.natAddCarry
        x.2.val x.1.1.quotientScratch.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (productRowAddCarryWorkLayout n) x
  have hflagState : x.1.1.flag = false := by
    simpa using hflag
  change ((productRowWorkspaceCarryWorkWord n).bit j).get stage =
    PlainAdder.Schedule.PowerOfTwo.natAddCarry
      x.2.val x.1.1.quotientScratch.val (j.val + 1)
  have hmain :
      ∀ m, ∀ j : Fin (n - 1), j.val = m ->
        ((productRowWorkspaceCarryWorkWord n).bit j).get stage =
          PlainAdder.Schedule.PowerOfTwo.natAddCarry
            x.2.val x.1.1.quotientScratch.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (productRowAddCarryWorkLayout n) j x hwork
        change ((productRowAddCarryWorkLayout n).workCarry.bit j).get
            ((productRowAddCarryWorkLayout n).carryStageIndexStep x) =
          PlainAdder.Schedule.PowerOfTwo.natAddCarry
            x.2.val x.1.1.quotientScratch.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (productRowAddCarryWorkLayout n) x
          rw [hdata]
          simp [productRowAddCarryWorkLayout,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            PlainAdder.Schedule.PowerOfTwo.natAddCarry, hzero, hflagState]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec' :
              ((productRowAddCarryWorkLayout n).workCarry.bit p).get
                  ((productRowAddCarryWorkLayout n).carryStageIndexStep x) =
            PlainAdder.Schedule.PowerOfTwo.natAddCarry
                  x.2.val x.1.1.quotientScratch.val (p.val + 1) := by
            simpa [stage, productRowAddCarryWorkLayout] using hpRec
          rw [hpRec', hpSucc]
          simp [productRowAddCarryWorkLayout,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            PlainAdder.Schedule.PowerOfTwo.natAddCarry]
  exact hmain j.val j rfl

/-- Carry selected before each quotient-scratch sum bit in the product-row
adder layout. -/
theorem productRowAddCarryBeforeSum_get_natAddCarry
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (productRowAddCarryWorkLayout n) i).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (productRowAddCarryWorkLayout n) x) =
      PlainAdder.Schedule.PowerOfTwo.natAddCarry
        x.2.val x.1.1.quotientScratch.val i.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  have hflagState : x.1.1.flag = false := by
    simpa using hflag
  by_cases hzero : i.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (productRowAddCarryWorkLayout n) x
    rw [hdata]
    change x.1.1.flag =
      PlainAdder.Schedule.PowerOfTwo.natAddCarry
        x.2.val x.1.1.quotientScratch.val i.val
    rw [hflagState]
    simp [PlainAdder.Schedule.PowerOfTwo.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : i.val - 1 < n - 1 := by
      have hi := i.isLt
      omega
    let j : Fin (n - 1) := ⟨i.val - 1, hjLt⟩
    have hcarry :=
      productRowAddCarryStage_get_workCarry_natAddCarry
        n j x hflag hwork
    have hjSucc : j.val + 1 = i.val := by
      dsimp [j]
      omega
    change ((productRowWorkspaceCarryWorkWord n).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (productRowAddCarryWorkLayout n) x) =
      PlainAdder.Schedule.PowerOfTwo.natAddCarry
        x.2.val x.1.1.quotientScratch.val i.val
    rw [hcarry, hjSucc]

/-- Clean flag/work endpoint for the quotient-scratch bits of one product-row
adder call. -/
theorem productRowAddStep_get_quotientScratch_add_row_testBit
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowAddStep n x).1.1.quotientScratch.val.testBit i.val =
      (x.1.1.quotientScratch + x.2).val.testBit i.val := by
  rw [← productRowWorkspaceQuotientScratchBit_get_testBit n i
    (productRowAddStep n x)]
  rw [productRowAddStep_get_quotientScratchBit n i x]
  rw [productRowAddCarryBeforeSum_get_natAddCarry n i x hflag hwork]
  simpa using
    (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
      n x.2 x.1.1.quotientScratch i).symm

/-- Clean flag/work endpoint for one product-row adder call: it adds the
loaded row into quotient scratch. -/
theorem productRowAddStep_get_quotientScratch_add_row
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowAddStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch + x.2 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  exact productRowAddStep_get_quotientScratch_add_row_testBit
    n i x hflag hwork

/-- The product-row adder preserves any observed readout disjoint from the
quotient-scratch targets and the temporary carry-work targets. -/
theorem productRowAddStep_get_observed_of_quotient_carry_ne
    (n : Nat) (observed : EncodedBit (pipelineWithProductRowWorkEncoding n))
    (hright :
      ∀ i : Fin n,
        ((productRowWorkspaceQuotientScratchWord n).bit i).wire ≠
          observed.wire)
    (hwork :
      ∀ j : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit j).wire ≠
          observed.wire)
    (x : PipelineWithProductRowWork n) :
    observed.get (productRowAddStep n x) = observed.get x := by
  unfold productRowAddStep
  exact
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (productRowAddCarryWorkLayout n) observed hright hwork x

/-- The product-row adder restores clean temporary carry work when started
with clean carry work. -/
theorem productRowAddStep_get_carryWork_clean
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowAddStep n x) =
      false := by
  unfold productRowAddStep
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (productRowAddCarryWorkLayout n) j x hwork
  simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    productRowAddCarryWorkLayout] using h

/-- Adding the loaded product row preserves the cleanup flag. -/
theorem productRowAddStep_get_flagBit
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get (productRowAddStep n x) =
      (productRowWorkspaceFlagBit n).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      (productRowWorkspaceFlagBit n)
      (fun i => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit i)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              (productFlagBit n)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productQuotientScratchWord n).bit i) (productFlagBit n)
            (productQuotientScratchBit_ne_flag n i))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              (productFlagBit n)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productCarryWorkWord n).bit j) (productFlagBit n)
            (Ne.symm (productFlagBit_ne_carryWork n j)))
      x

/-- Adding the loaded row into quotient scratch preserves a target readout. -/
theorem productRowAddStep_get_targetBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit bit).get (productRowAddStep n x) =
      ((productRowWorkspaceTargetWord n).bit bit).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      ((productRowWorkspaceTargetWord n).bit bit)
      (fun i => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit i)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productTargetWord n).bit bit)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productQuotientScratchWord n).bit i)
            ((productTargetWord n).bit bit)
            (productQuotientScratchBit_ne_target n i bit))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productTargetWord n).bit bit)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)
            ((productTargetWord n).bit bit)
            (productCarryWorkBit_ne_target n j bit))
      x

/-- Adding the loaded row into quotient scratch preserves the target field. -/
theorem productRowAddStep_get_target
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowAddStep n x).1.1.target = x.1.1.target := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceTargetBit_get_testBit n bit
    (productRowAddStep n x)]
  rw [productRowAddStep_get_targetBit n bit x]
  exact productRowWorkspaceTargetBit_get_testBit n bit x

/-- Adding the loaded row into quotient scratch preserves the denominator. -/
theorem productRowAddCarryOutGatesAt_get_denominator
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n) :
    (EncodedBit.GateSpec.stepList
        (PlainAdder.Schedule.CarryWorkLayout.carryOutGatesAt
          (productRowAddCarryWorkLayout n) j) x).1.1.denominator =
      x.1.1.denominator := by
  exact EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun y : PipelineWithProductRowWork n => y.1.1.denominator)
    (gates :=
      PlainAdder.Schedule.CarryWorkLayout.carryOutGatesAt
        (productRowAddCarryWorkLayout n) j)
    (by
      intro gate hgate
      have hcases := by
        simpa [PlainAdder.Schedule.CarryWorkLayout.carryOutGatesAt,
          productRowAddCarryWorkLayout, BitSlice.Encoded.carryOutGates] using
          hgate
      rcases hcases with hgate | hgate | hgate <;>
        subst gate <;>
        simp [EncodedBit.GateSpec.targetFlipPreserves])
    x

theorem productRowAddCarryStageIndexStep_get_denominator
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
        (productRowAddCarryWorkLayout n) x).1.1.denominator =
      x.1.1.denominator := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
  induction PlainAdder.Schedule.CarryWorkLayout.carryStageIndices
    generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (rest.foldl
            (fun y j =>
              EncodedBit.GateSpec.stepList
                (PlainAdder.Schedule.CarryWorkLayout.carryOutGatesAt
                  (productRowAddCarryWorkLayout n) j) y)
            (EncodedBit.GateSpec.stepList
              (PlainAdder.Schedule.CarryWorkLayout.carryOutGatesAt
                (productRowAddCarryWorkLayout n) j) x)).1.1.denominator =
          x.1.1.denominator
      rw [ih]
      exact productRowAddCarryOutGatesAt_get_denominator n j x

theorem productRowAddSumGatesAt_get_denominator
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n) :
    (EncodedBit.GateSpec.stepList
        (PlainAdder.Schedule.CarryWorkLayout.sumGatesAt
          (productRowAddCarryWorkLayout n) i) x).1.1.denominator =
      x.1.1.denominator := by
  exact EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun y : PipelineWithProductRowWork n => y.1.1.denominator)
    (gates :=
      PlainAdder.Schedule.CarryWorkLayout.sumGatesAt
        (productRowAddCarryWorkLayout n) i)
    (by
      intro gate hgate
      have hcases := by
        simpa [PlainAdder.Schedule.CarryWorkLayout.sumGatesAt,
          productRowAddCarryWorkLayout, BitSlice.Encoded.sumGates] using hgate
      rcases hcases with hgate | hgate <;>
        subst gate <;>
        simp [EncodedBit.GateSpec.targetFlipPreserves])
    x

theorem productRowAddCarryOutCleanupGatesAt_get_denominator
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n) :
    (EncodedBit.GateSpec.stepList
        (PlainAdder.Schedule.CarryWorkLayout.carryOutCleanupGatesAt
          (productRowAddCarryWorkLayout n) j) x).1.1.denominator =
      x.1.1.denominator := by
  exact EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun y : PipelineWithProductRowWork n => y.1.1.denominator)
    (gates :=
      PlainAdder.Schedule.CarryWorkLayout.carryOutCleanupGatesAt
        (productRowAddCarryWorkLayout n) j)
    (by
      intro gate hgate
      have hcases := by
        simpa [PlainAdder.Schedule.CarryWorkLayout.carryOutCleanupGatesAt,
          productRowAddCarryWorkLayout, BitSlice.Encoded.carryOutCleanupGates,
          BitSlice.Encoded.carryOutGates] using hgate
      rcases hcases with hgate | hgate | hgate <;>
        subst gate <;>
        simp [EncodedBit.GateSpec.targetFlipPreserves])
    x

theorem productRowAddCleanupSumGatesAt_get_denominator
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n) :
    (EncodedBit.GateSpec.stepList
        (PlainAdder.Schedule.CarryWorkLayout.cleanupSumGatesAt
          (productRowAddCarryWorkLayout n) i) x).1.1.denominator =
      x.1.1.denominator := by
  unfold PlainAdder.Schedule.CarryWorkLayout.cleanupSumGatesAt
  by_cases hzero : i.val = 0
  · simpa [hzero] using productRowAddSumGatesAt_get_denominator n i x
  · rw [dif_neg hzero]
    rw [EncodedBit.GateSpec.stepList_append]
    rw [productRowAddCarryOutCleanupGatesAt_get_denominator]
    exact productRowAddSumGatesAt_get_denominator n i x

theorem productRowAddCleanupSumStageIndexStep_get_denominator
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (PlainAdder.Schedule.CarryWorkLayout.cleanupSumStageIndexStep
        (productRowAddCarryWorkLayout n) x).1.1.denominator =
      x.1.1.denominator := by
  unfold PlainAdder.Schedule.CarryWorkLayout.cleanupSumStageIndexStep
  induction PlainAdder.Schedule.CarryWorkLayout.cleanupSumStageIndices
    generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        (rest.foldl
            (fun y i =>
              EncodedBit.GateSpec.stepList
                (PlainAdder.Schedule.CarryWorkLayout.cleanupSumGatesAt
                  (productRowAddCarryWorkLayout n) i) y)
            (EncodedBit.GateSpec.stepList
              (PlainAdder.Schedule.CarryWorkLayout.cleanupSumGatesAt
                (productRowAddCarryWorkLayout n) i) x)).1.1.denominator =
          x.1.1.denominator
      rw [ih]
      exact productRowAddCleanupSumGatesAt_get_denominator n i x

theorem productRowAddStep_get_denominator
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowAddStep n x).1.1.denominator = x.1.1.denominator := by
  unfold productRowAddStep PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
  rw [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_stepList_eq_indexStep]
  rw [productRowAddCleanupSumStageIndexStep_get_denominator]
  exact productRowAddCarryStageIndexStep_get_denominator n x

/-- Adding the loaded row into quotient scratch preserves the shifted-row
readout used by the subsequent unload. -/
theorem productRowAddStep_get_shiftedRowBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowAddStep n x) =
      ((productRowWorkspaceShiftedRowWord n offset).bit i).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      ((productRowWorkspaceShiftedRowWord n offset).bit i)
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit (shiftedRowIndex offset i))).wire
        exact
          productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)
            ((productRowWord n).bit (shiftedRowIndex offset i)))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit (shiftedRowIndex offset i))).wire
        exact
          productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)
            ((productRowWord n).bit (shiftedRowIndex offset i)))
      x

/-- Adding the loaded row into quotient scratch preserves every product-row
bit. -/
theorem productRowAddStep_get_rowBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit bit).get (productRowAddStep n x) =
      ((productRowWorkspaceRowWord n).bit bit).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      ((productRowWorkspaceRowWord n).bit bit)
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit bit)).wire
        exact
          productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)
            ((productRowWord n).bit bit))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspaceBit n (productRowEncoding n)
              ((productRowWord n).bit bit)).wire
        exact
          productWorkspacePipelineBit_ne_productBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)
            ((productRowWord n).bit bit))
      x

/-- Adding the product row preserves an inverse-scratch readout. -/
theorem productRowAddStep_get_inverseScratchBit
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowAddStep n x) =
      ((productRowWorkspaceInverseScratchWord n).bit i).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      ((productRowWorkspaceInverseScratchWord n).bit i)
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productInverseScratchWord n).bit i)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)
            ((productInverseScratchWord n).bit i)
            (Ne.symm (productInverseScratchBit_ne_quotientScratch n i j)))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productInverseScratchWord n).bit i)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)
            ((productInverseScratchWord n).bit i)
            (Ne.symm (productInverseScratchBit_ne_carryWork n i j)))
      x

/-- Adding the product row preserves a numerator readout. -/
theorem productRowAddStep_get_numeratorBit
    (n : Nat) (i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowAddStep n x) =
      ((productRowWorkspaceNumeratorWord n).bit i).get x := by
  exact
    productRowAddStep_get_observed_of_quotient_carry_ne n
      ((productRowWorkspaceNumeratorWord n).bit i)
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productNumeratorWord n).bit i)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productQuotientScratchWord n).bit j)
            ((productNumeratorWord n).bit i)
            (Ne.symm (productNumeratorBit_ne_quotientScratch n i j)))
      (fun j => by
        change
          (productWorkspacePipelineBit n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n)
              ((productNumeratorWord n).bit i)).wire
        exact
          productWorkspacePipelineBit_ne_of_ne n (productRowEncoding n)
            ((productCarryWorkWord n).bit j)
            ((productNumeratorWord n).bit i)
            (Ne.symm (productNumeratorBit_ne_carryWork n i j)))
      x

/-- The product-row adder program realizes its folded carry/sum/cleanup
semantics. -/
theorem productRowAdd_realizes (n : Nat) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowAddProgram n) (productRowAddStep n) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes
    (productRowAddCarryWorkLayout n)

/-- Same-Circuit witness for adding a loaded product row into quotient
scratch. -/
def productRowAddSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowAddStep n) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowAddProgram n
  realizes := productRowAdd_realizes n

/-! #### One-offset product-row add slice -/

/-- Reverse gate list for unloading one shifted product row after the row has
been added into quotient scratch. -/
def productRowControlledShiftedUnloadGates (n : Nat) (offset : Fin n) :
    List (EncodedBit.GateSpec (pipelineWithProductRowWorkEncoding n)) :=
  (productRowControlledShiftedLoadGates n offset).reverse

/-- Base-gate program for unloading one shifted product row. -/
def productRowControlledShiftedUnloadProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  EncodedBit.GateSpec.programList
    (productRowControlledShiftedUnloadGates n offset)

/-- Folded semantic action for unloading one shifted product row. -/
def productRowControlledShiftedUnloadStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  EncodedBit.GateSpec.stepList
    (productRowControlledShiftedUnloadGates n offset)

/-- A shifted product-row unload toggles each shifted row target by the
corresponding controlled numerator bit. -/
theorem productRowControlledShiftedUnloadStep_get_shiftedRowBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowControlledShiftedUnloadStep n offset x) =
      (((productRowWorkspaceShiftedRowWord n offset).bit i).get x ^^
        (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
          ((productRowWorkspaceNumeratorWord n).bit i).get x)) := by
  unfold productRowControlledShiftedUnloadStep
    productRowControlledShiftedUnloadGates
    productRowControlledShiftedLoadGates controlledShiftedRowLoadGates
  exact
    EncodedBit.Word.controlledXorIntoGates_reverse_get_target
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceShiftedRowWord n offset)
      (productRowWorkspaceInverseScratch_ne_numerator n offset)
      (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
      (productRowWorkspaceNumerator_ne_shiftedRow n offset)
      i
      (fun j hji => productRowWorkspaceShiftedRow_ne_of_ne n offset hji)
      (fun j => Ne.symm (productRowWorkspaceInverseScratch_ne_shiftedRow n offset j))
      (fun j =>
        Ne.symm
          (productRowWorkspaceNumerator_ne_shiftedRow_of_bits n offset i j))
      x

/-- A shifted product-row unload preserves any observed readout disjoint from
the shifted row targets. -/
theorem productRowControlledShiftedUnloadStep_get_observed_of_shiftedRow_ne
    (n : Nat) (offset : Fin n)
    (observed : EncodedBit (pipelineWithProductRowWorkEncoding n))
    (hne :
      ∀ i,
        ((productRowWorkspaceShiftedRowWord n offset).bit i).wire ≠
          observed.wire)
    (x : PipelineWithProductRowWork n) :
    observed.get (productRowControlledShiftedUnloadStep n offset x) =
      observed.get x := by
  unfold productRowControlledShiftedUnloadStep
    productRowControlledShiftedUnloadGates
    productRowControlledShiftedLoadGates controlledShiftedRowLoadGates
  exact
    EncodedBit.Word.controlledXorIntoGates_reverse_get_observed_of_target_ne
      ((productRowWorkspaceInverseScratchWord n).bit offset)
      (productRowWorkspaceNumeratorWord n)
      (productRowWorkspaceShiftedRowWord n offset)
      (productRowWorkspaceInverseScratch_ne_numerator n offset)
      (productRowWorkspaceInverseScratch_ne_shiftedRow n offset)
      (productRowWorkspaceNumerator_ne_shiftedRow n offset)
      observed hne x

/-- A shifted product-row unload writes only the trailing row workspace; every
pipeline-register readout is preserved. -/
theorem productRowControlledShiftedUnloadStep_get_pipelineBit
    (n : Nat) (offset : Fin n)
    (bit : EncodedBit (pipelineWithWorkSameCircuit n).encoding)
    (x : PipelineWithProductRowWork n) :
    (productWorkspacePipelineBit n (productRowEncoding n) bit).get
        (productRowControlledShiftedUnloadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n) bit).get x := by
  exact
    productRowControlledShiftedUnloadStep_get_observed_of_shiftedRow_ne
      n offset (productWorkspacePipelineBit n (productRowEncoding n) bit)
      (fun i => by
        change
          (productWorkspaceBit n (productRowEncoding n)
            ((productRowWord n).bit (shiftedRowIndex offset i))).wire ≠
            (productWorkspacePipelineBit n (productRowEncoding n) bit).wire
        exact
          Ne.symm
            (productWorkspacePipelineBit_ne_productBit n
              (productRowEncoding n) bit
              ((productRowWord n).bit (shiftedRowIndex offset i))))
      x

/-- A shifted product-row unload preserves the quotient-scratch word. -/
theorem productRowControlledShiftedUnloadStep_get_quotientScratch
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowControlledShiftedUnloadStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceQuotientScratchBit_get_testBit n bit
      (productRowControlledShiftedUnloadStep n offset x)]
  have hbit :
      ((productRowWorkspaceQuotientScratchWord n).bit bit).get
          (productRowControlledShiftedUnloadStep n offset x) =
        ((productRowWorkspaceQuotientScratchWord n).bit bit).get x := by
    simpa [productRowWorkspaceQuotientScratchWord,
      productWorkspaceQuotientScratchWord, productWorkspacePipelineWord] using
      productRowControlledShiftedUnloadStep_get_pipelineBit n offset
        ((productQuotientScratchWord n).bit bit) x
  rw [hbit]
  exact productRowWorkspaceQuotientScratchBit_get_testBit n bit x

/-- A shifted product-row unload preserves the cleanup flag. -/
theorem productRowControlledShiftedUnloadStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowControlledShiftedUnloadStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  simpa [productRowWorkspaceFlagBit, productWorkspaceFlagBit] using
    productRowControlledShiftedUnloadStep_get_pipelineBit n offset
      (productFlagBit n) x

/-- A shifted product-row unload preserves each temporary carry-work bit. -/
theorem productRowControlledShiftedUnloadStep_get_carryWorkBit
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowControlledShiftedUnloadStep n offset x) =
      ((productRowWorkspaceCarryWorkWord n).bit j).get x := by
  simpa [productRowWorkspaceCarryWorkWord, productWorkspaceCarryWorkWord,
    productWorkspacePipelineWord] using
    productRowControlledShiftedUnloadStep_get_pipelineBit n offset
      ((productCarryWorkWord n).bit j) x

/-- The unload program realizes its folded reverse-Toffoli semantics. -/
theorem productRowControlledShiftedUnload_realizes
    (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowControlledShiftedUnloadProgram n offset)
      (productRowControlledShiftedUnloadStep n offset) :=
  EncodedBit.GateSpec.realizesList
    (productRowControlledShiftedUnloadGates n offset)

/-- Same-Circuit witness for unloading one shifted product row. -/
def productRowControlledShiftedUnloadSameCircuit (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowControlledShiftedUnloadStep n offset) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowControlledShiftedUnloadProgram n offset
  realizes := productRowControlledShiftedUnload_realizes n offset

/-! #### One-offset non-wrapping product-row add slice -/

/-- Folded semantic action for one quotient-product row slice using the
non-wrapping filtered product-row load: load a low-bit partial-product row, add
it into quotient scratch, then unload the same filtered row. -/
def productRowTruncatedOffsetAddStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  fun x =>
    productRowTruncatedShiftedUnloadStep n offset
      (productRowAddStep n
        (productRowTruncatedShiftedLoadStep n offset x))

/-- Base-gate program for one non-wrapping quotient-product row slice. -/
def productRowTruncatedOffsetAddProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  BaseGateProgram.append (productRowTruncatedShiftedLoadProgram n offset)
    (BaseGateProgram.append (productRowAddProgram n)
      (productRowTruncatedShiftedUnloadProgram n offset))

/-- The non-wrapping one-offset row-slice program realizes its folded
load/add/unload semantics, tying correctness and resource accounting to the
same filtered gate object [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618]. -/
theorem productRowTruncatedOffsetAdd_realizes (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowTruncatedOffsetAddProgram n offset)
      (productRowTruncatedOffsetAddStep n offset) := by
  have htail :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (BaseGateProgram.append (productRowAddProgram n)
          (productRowTruncatedShiftedUnloadProgram n offset))
        (fun x : PipelineWithProductRowWork n =>
          productRowTruncatedShiftedUnloadStep n offset
            (productRowAddStep n x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := productRowAddStep n)
      (secondStep := productRowTruncatedShiftedUnloadStep n offset)
      (productRowAdd_realizes n)
      (productRowTruncatedShiftedUnload_realizes n offset)
  have hfull :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (productRowTruncatedOffsetAddProgram n offset)
        (productRowTruncatedOffsetAddStep n offset) :=
    BaseGateProgram.Realizes.append
      (firstStep := productRowTruncatedShiftedLoadStep n offset)
      (secondStep := fun x : PipelineWithProductRowWork n =>
        productRowTruncatedShiftedUnloadStep n offset
          (productRowAddStep n x))
      (productRowTruncatedShiftedLoad_realizes n offset)
      htail
  simpa [productRowTruncatedOffsetAddProgram,
    productRowTruncatedOffsetAddStep] using hfull

/-- Same-Circuit witness for one non-wrapping quotient-product row slice. -/
def productRowTruncatedOffsetAddSameCircuit (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowTruncatedOffsetAddStep n offset) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowTruncatedOffsetAddProgram n offset
  realizes := productRowTruncatedOffsetAdd_realizes n offset

/-- One non-wrapping load/add/unload row slice preserves an inverse-scratch
readout. -/
theorem productRowTruncatedOffsetAddStep_get_inverseScratchBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowTruncatedOffsetAddStep n offset x) =
      ((productRowWorkspaceInverseScratchWord n).bit i).get x := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_inverseScratchBit]
  rw [productRowAddStep_get_inverseScratchBit]
  rw [productRowTruncatedShiftedLoadStep_get_inverseScratchBit]

/-- One non-wrapping load/add/unload row slice preserves a numerator readout. -/
theorem productRowTruncatedOffsetAddStep_get_numeratorBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowTruncatedOffsetAddStep n offset x) =
      ((productRowWorkspaceNumeratorWord n).bit i).get x := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_numeratorBit]
  rw [productRowAddStep_get_numeratorBit]
  rw [productRowTruncatedShiftedLoadStep_get_numeratorBit]

/-- One non-wrapping load/add/unload row slice preserves a target readout. -/
theorem productRowTruncatedOffsetAddStep_get_targetBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit i).get
        (productRowTruncatedOffsetAddStep n offset x) =
      ((productRowWorkspaceTargetWord n).bit i).get x := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_targetBit]
  rw [productRowAddStep_get_targetBit]
  rw [productRowTruncatedShiftedLoadStep_get_targetBit]

/-- One non-wrapping load/add/unload row slice preserves the target field. -/
theorem productRowTruncatedOffsetAddStep_get_target
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedOffsetAddStep n offset x).1.1.target =
      x.1.1.target := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceTargetBit_get_testBit n bit
    (productRowTruncatedOffsetAddStep n offset x)]
  rw [productRowTruncatedOffsetAddStep_get_targetBit n offset bit x]
  exact productRowWorkspaceTargetBit_get_testBit n bit x

/-- One non-wrapping load/add/unload row slice preserves the denominator. -/
theorem productRowTruncatedOffsetAddStep_get_denominator
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedOffsetAddStep n offset x).1.1.denominator =
      x.1.1.denominator := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_denominator]
  rw [productRowAddStep_get_denominator]
  rw [productRowTruncatedShiftedLoadStep_get_denominator]

/-- One non-wrapping row slice preserves every future clean loaded-row value. -/
theorem productRowTruncatedCleanLoadedRow_eq_after_offset
    (n : Nat) (future offset : Fin n) (x : PipelineWithProductRowWork n) :
    productRowTruncatedCleanLoadedRow n future
        (productRowTruncatedOffsetAddStep n offset x) =
      productRowTruncatedCleanLoadedRow n future x := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro target
  by_cases htarget :
      ∃ bit : Fin n, ∃ h : bit.val + future.val < n,
        truncatedShiftedRowIndex future bit h = target
  · rcases htarget with ⟨bit, h, hidx⟩
    rw [← hidx]
    rw [productRowTruncatedCleanLoadedRow_get_truncatedBit]
    rw [productRowTruncatedCleanLoadedRow_get_truncatedBit]
    rw [productRowTruncatedOffsetAddStep_get_inverseScratchBit]
    rw [productRowTruncatedOffsetAddStep_get_numeratorBit]
  · have hne :
        ∀ bit : Fin n, ∀ h : bit.val + future.val < n,
          truncatedShiftedRowIndex future bit h ≠ target := by
      intro bit h hidx
      exact htarget ⟨bit, h, hidx⟩
    rw [productRowTruncatedCleanLoadedRow_get_rowBit_of_target_ne
      n future target hne]
    rw [productRowTruncatedCleanLoadedRow_get_rowBit_of_target_ne
      n future target hne]

/-- One non-wrapping load/add/unload row slice preserves the cleanup flag. -/
theorem productRowTruncatedOffsetAddStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowTruncatedOffsetAddStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_flagBit]
  rw [productRowAddStep_get_flagBit]
  rw [productRowTruncatedShiftedLoadStep_get_flagBit]

/-- One non-wrapping load/add/unload row slice restores clean temporary carry
work when started from clean carry work. -/
theorem productRowTruncatedOffsetAddStep_get_carryWork_clean
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowTruncatedOffsetAddStep n offset x) =
      false := by
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_carryWorkBit]
  apply productRowAddStep_get_carryWork_clean
  intro k
  rw [productRowTruncatedShiftedLoadStep_get_carryWorkBit]
  exact hwork k

/-- One non-wrapping load/add/unload row slice restores a clean product row. -/
theorem productRowTruncatedOffsetAddStep_get_row_clean
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowTruncatedOffsetAddStep n offset x).2 = 0 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro target
  rw [← productRowWorkspaceRowBit_get_testBit n target
    (productRowTruncatedOffsetAddStep n offset x)]
  by_cases htarget :
      ∃ bit : Fin n, ∃ h : bit.val + offset.val < n,
        truncatedShiftedRowIndex offset bit h = target
  · rcases htarget with ⟨bit, h, hidx⟩
    rw [← hidx]
    unfold productRowTruncatedOffsetAddStep
    rw [productRowTruncatedShiftedUnloadStep_get_truncatedRowBit]
    rw [productRowAddStep_get_rowBit]
    rw [productRowAddStep_get_inverseScratchBit]
    rw [productRowAddStep_get_numeratorBit]
    rw [productRowTruncatedShiftedLoadStep_get_truncatedRowBit]
    rw [productRowTruncatedShiftedLoadStep_get_inverseScratchBit]
    rw [productRowTruncatedShiftedLoadStep_get_numeratorBit]
    have hrowBit :
        ((productRowWorkspaceRowWord n).bit
            (truncatedShiftedRowIndex offset bit h)).get x = false := by
      rw [productRowWorkspaceRowBit_get_testBit]
      simp [hrow]
    rw [hrowBit]
    cases hcond :
        (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
          ((productRowWorkspaceNumeratorWord n).bit bit).get x) <;>
      simp
  · have hne :
        ∀ bit : Fin n, ∀ h : bit.val + offset.val < n,
          truncatedShiftedRowIndex offset bit h ≠ target := by
      intro bit h hidx
      exact htarget ⟨bit, h, hidx⟩
    unfold productRowTruncatedOffsetAddStep
    rw [productRowTruncatedShiftedUnloadStep_get_rowBit_of_target_ne
      n offset target hne]
    rw [productRowAddStep_get_rowBit]
    rw [productRowTruncatedShiftedLoadStep_get_rowBit_of_target_ne
      n offset target hne]
    rw [productRowWorkspaceRowBit_get_testBit]
    simp [hrow]

/-- Clean flag/work endpoint for one non-wrapping row slice: the quotient
scratch receives the row loaded by the filtered shifted-copy stage. -/
theorem productRowTruncatedOffsetAddStep_get_quotientScratch_add_loadedRow
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowTruncatedOffsetAddStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        (productRowTruncatedShiftedLoadStep n offset x).2 := by
  have hflagLoad :
      (productRowWorkspaceFlagBit n).get
          (productRowTruncatedShiftedLoadStep n offset x) = false := by
    rw [productRowTruncatedShiftedLoadStep_get_flagBit]
    exact hflag
  have hworkLoad :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get
            (productRowTruncatedShiftedLoadStep n offset x) = false := by
    intro k
    rw [productRowTruncatedShiftedLoadStep_get_carryWorkBit]
    exact hwork k
  unfold productRowTruncatedOffsetAddStep
  rw [productRowTruncatedShiftedUnloadStep_get_quotientScratch]
  rw [productRowAddStep_get_quotientScratch_add_row n
    (productRowTruncatedShiftedLoadStep n offset x) hflagLoad hworkLoad]
  rw [productRowTruncatedShiftedLoadStep_get_quotientScratch]

/-- Folded semantic action for one quotient-product row slice:
load a shifted row, add it into quotient scratch, then unload the row
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350,591-618]. -/
def productRowOffsetAddStep (n : Nat) (offset : Fin n) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  fun x =>
    productRowControlledShiftedUnloadStep n offset
      (productRowAddStep n
        (productRowControlledShiftedLoadStep n offset x))

/-- One load/add/unload row slice restores the shifted row bit. -/
theorem productRowOffsetAddStep_get_shiftedRowBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceShiftedRowWord n offset).bit i).get
        (productRowOffsetAddStep n offset x) =
      ((productRowWorkspaceShiftedRowWord n offset).bit i).get x := by
  unfold productRowOffsetAddStep
  rw [productRowControlledShiftedUnloadStep_get_shiftedRowBit]
  rw [productRowAddStep_get_shiftedRowBit]
  rw [productRowAddStep_get_inverseScratchBit]
  rw [productRowAddStep_get_numeratorBit]
  rw [productRowControlledShiftedLoadStep_get_shiftedRowBit]
  have hcontrol :
      ((productRowWorkspaceInverseScratchWord n).bit offset).get
          (productRowControlledShiftedLoadStep n offset x) =
        ((productRowWorkspaceInverseScratchWord n).bit offset).get x := by
    simpa [productRowWorkspaceInverseScratchWord,
      productWorkspaceInverseScratchWord, productWorkspacePipelineWord] using
      productRowControlledShiftedLoadStep_get_pipelineBit n offset
        ((productInverseScratchWord n).bit offset) x
  have hsource :
      ((productRowWorkspaceNumeratorWord n).bit i).get
          (productRowControlledShiftedLoadStep n offset x) =
        ((productRowWorkspaceNumeratorWord n).bit i).get x := by
    simpa [productRowWorkspaceNumeratorWord,
      productWorkspaceNumeratorWord, productWorkspacePipelineWord] using
      productRowControlledShiftedLoadStep_get_pipelineBit n offset
        ((productNumeratorWord n).bit i) x
  rw [hcontrol, hsource]
  cases hrow : ((productRowWorkspaceShiftedRowWord n offset).bit i).get x <;>
  cases hcond :
      (((productRowWorkspaceInverseScratchWord n).bit offset).get x &&
        ((productRowWorkspaceNumeratorWord n).bit i).get x) <;>
    simp

/-- One load/add/unload row slice preserves every product-row bit. -/
theorem productRowOffsetAddStep_get_rowBit
    (n : Nat) (offset bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit bit).get
        (productRowOffsetAddStep n offset x) =
      ((productRowWorkspaceRowWord n).bit bit).get x := by
  obtain ⟨shiftedBit, hshifted⟩ := shiftedRowIndex_surjective offset bit
  rw [← hshifted]
  simpa [productRowWorkspaceShiftedRowWord] using
    productRowOffsetAddStep_get_shiftedRowBit n offset shiftedBit x

/-- One load/add/unload row slice preserves the product-row workspace value. -/
theorem productRowOffsetAddStep_get_row
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowOffsetAddStep n offset x).2 = x.2 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceRowBit_get_testBit n bit
      (productRowOffsetAddStep n offset x)]
  rw [productRowOffsetAddStep_get_rowBit n offset bit x]
  exact productRowWorkspaceRowBit_get_testBit n bit x

/-- One load/add/unload row slice preserves an inverse-scratch readout. -/
theorem productRowOffsetAddStep_get_inverseScratchBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowOffsetAddStep n offset x) =
      ((productRowWorkspaceInverseScratchWord n).bit i).get x := by
  unfold productRowOffsetAddStep
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit i)).get
        (productRowControlledShiftedUnloadStep n offset
          (productRowAddStep n
            (productRowControlledShiftedLoadStep n offset x))) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit i)).get x
  rw [productRowControlledShiftedUnloadStep_get_pipelineBit]
  change
    ((productRowWorkspaceInverseScratchWord n).bit i).get
        (productRowAddStep n
          (productRowControlledShiftedLoadStep n offset x)) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit i)).get x
  rw [productRowAddStep_get_inverseScratchBit]
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit i)).get
        (productRowControlledShiftedLoadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productInverseScratchWord n).bit i)).get x
  rw [productRowControlledShiftedLoadStep_get_pipelineBit]

/-- One load/add/unload row slice preserves a numerator readout. -/
theorem productRowOffsetAddStep_get_numeratorBit
    (n : Nat) (offset i : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowOffsetAddStep n offset x) =
      ((productRowWorkspaceNumeratorWord n).bit i).get x := by
  unfold productRowOffsetAddStep
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).get
        (productRowControlledShiftedUnloadStep n offset
          (productRowAddStep n
            (productRowControlledShiftedLoadStep n offset x))) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).get x
  rw [productRowControlledShiftedUnloadStep_get_pipelineBit]
  change
    ((productRowWorkspaceNumeratorWord n).bit i).get
        (productRowAddStep n
          (productRowControlledShiftedLoadStep n offset x)) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).get x
  rw [productRowAddStep_get_numeratorBit]
  change
    (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).get
        (productRowControlledShiftedLoadStep n offset x) =
      (productWorkspacePipelineBit n (productRowEncoding n)
        ((productNumeratorWord n).bit i)).get x
  rw [productRowControlledShiftedLoadStep_get_pipelineBit]

/-- One row slice preserves every future clean loaded-row value. -/
theorem productRowCleanLoadedRow_eq_after_offset
    (n : Nat) (future offset : Fin n) (x : PipelineWithProductRowWork n) :
    productRowCleanLoadedRow n future (productRowOffsetAddStep n offset x) =
      productRowCleanLoadedRow n future x := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  obtain ⟨i, hi⟩ := shiftedRowIndex_surjective future bit
  rw [← hi]
  rw [productRowCleanLoadedRow_get_shiftedBit]
  rw [productRowCleanLoadedRow_get_shiftedBit]
  rw [productRowOffsetAddStep_get_inverseScratchBit]
  rw [productRowOffsetAddStep_get_numeratorBit]

/-- One load/add/unload row slice preserves the cleanup flag. -/
theorem productRowOffsetAddStep_get_flagBit
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowOffsetAddStep n offset x) =
      (productRowWorkspaceFlagBit n).get x := by
  unfold productRowOffsetAddStep
  rw [productRowControlledShiftedUnloadStep_get_flagBit]
  rw [productRowAddStep_get_flagBit]
  rw [productRowControlledShiftedLoadStep_get_flagBit]

/-- One load/add/unload row slice restores clean temporary carry work when
started from clean carry work. -/
theorem productRowOffsetAddStep_get_carryWork_clean
    (n : Nat) (offset : Fin n) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowOffsetAddStep n offset x) =
      false := by
  unfold productRowOffsetAddStep
  rw [productRowControlledShiftedUnloadStep_get_carryWorkBit]
  apply productRowAddStep_get_carryWork_clean
  intro k
  rw [productRowControlledShiftedLoadStep_get_carryWorkBit]
  exact hwork k

/-- Clean flag/work endpoint for one load/add/unload row slice: the quotient
scratch receives the row loaded by the shifted copy stage. -/
theorem productRowOffsetAddStep_get_quotientScratch_add_loadedRow
    (n : Nat) (offset : Fin n) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowOffsetAddStep n offset x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        (productRowControlledShiftedLoadStep n offset x).2 := by
  have hflagLoad :
      (productRowWorkspaceFlagBit n).get
          (productRowControlledShiftedLoadStep n offset x) = false := by
    rw [productRowControlledShiftedLoadStep_get_flagBit]
    exact hflag
  have hworkLoad :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get
            (productRowControlledShiftedLoadStep n offset x) = false := by
    intro k
    rw [productRowControlledShiftedLoadStep_get_carryWorkBit]
    exact hwork k
  unfold productRowOffsetAddStep
  rw [productRowControlledShiftedUnloadStep_get_quotientScratch]
  rw [productRowAddStep_get_quotientScratch_add_row n
    (productRowControlledShiftedLoadStep n offset x) hflagLoad hworkLoad]
  rw [productRowControlledShiftedLoadStep_get_quotientScratch]

/-- Base-gate program for one quotient-product row slice. -/
def productRowOffsetAddProgram (n : Nat) (offset : Fin n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  BaseGateProgram.append (productRowControlledShiftedLoadProgram n offset)
    (BaseGateProgram.append (productRowAddProgram n)
      (productRowControlledShiftedUnloadProgram n offset))

/-- The one-offset row-slice program realizes its folded load/add/unload
semantics, tying correctness and resource accounting to the same gate object. -/
theorem productRowOffsetAdd_realizes (n : Nat) (offset : Fin n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowOffsetAddProgram n offset)
      (productRowOffsetAddStep n offset) := by
  have htail :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (BaseGateProgram.append (productRowAddProgram n)
          (productRowControlledShiftedUnloadProgram n offset))
        (fun x : PipelineWithProductRowWork n =>
          productRowControlledShiftedUnloadStep n offset
            (productRowAddStep n x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := productRowAddStep n)
      (secondStep := productRowControlledShiftedUnloadStep n offset)
      (productRowAdd_realizes n)
      (productRowControlledShiftedUnload_realizes n offset)
  have hfull :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (productRowOffsetAddProgram n offset)
        (productRowOffsetAddStep n offset) :=
    BaseGateProgram.Realizes.append
      (firstStep := productRowControlledShiftedLoadStep n offset)
      (secondStep := fun x : PipelineWithProductRowWork n =>
        productRowControlledShiftedUnloadStep n offset
          (productRowAddStep n x))
      (productRowControlledShiftedLoad_realizes n offset)
      htail
  simpa [productRowOffsetAddProgram, productRowOffsetAddStep] using hfull

/-- Same-Circuit witness for one quotient-product row slice. -/
def productRowOffsetAddSameCircuit (n : Nat) (offset : Fin n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowOffsetAddStep n offset) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowOffsetAddProgram n offset
  realizes := productRowOffsetAdd_realizes n offset

/-! #### Folded product-row program -/

/-- Offsets used by the shifted-row product program, in little-endian bit
order. -/
def productRowOffsets (n : Nat) : List (Fin n) :=
  List.ofFn fun offset : Fin n => offset

/-- Fold a list of product-row offsets into one non-wrapping base-gate
program. -/
def productRowTruncatedOffsetsProgram (n : Nat) :
    List (Fin n) -> BaseGateProgram (pipelineWithProductRowWorkEncoding n).width
  | [] => []
  | offset :: rest =>
      BaseGateProgram.append (productRowTruncatedOffsetAddProgram n offset)
        (productRowTruncatedOffsetsProgram n rest)

/-- Folded semantic action for a list of non-wrapping product-row offsets. -/
def productRowTruncatedOffsetsStep (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> PipelineWithProductRowWork n
  | [] => id
  | offset :: rest =>
      fun x =>
        productRowTruncatedOffsetsStep n rest
          (productRowTruncatedOffsetAddStep n offset x)

/-- Sum of the concrete rows loaded by a folded non-wrapping offset list. -/
def productRowTruncatedOffsetsLoadedSum (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> ProductRowWork n
  | [] => fun _ => 0
  | offset :: rest =>
      fun x =>
        (productRowTruncatedShiftedLoadStep n offset x).2 +
          productRowTruncatedOffsetsLoadedSum n rest
            (productRowTruncatedOffsetAddStep n offset x)

/-- Sum of non-wrapping clean loaded rows, all read from the same source
pipeline. -/
def productRowTruncatedOffsetsCleanLoadedSum (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> ProductRowWork n
  | [] => fun _ => 0
  | offset :: rest =>
      fun x =>
        productRowTruncatedCleanLoadedRow n offset x +
          productRowTruncatedOffsetsCleanLoadedSum n rest x

/-- Closed form for a folded list of non-wrapping clean loaded rows as a sum
of controlled shifted numerators. -/
theorem productRowTruncatedOffsetsCleanLoadedSum_eq_shiftedNumeratorListSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    productRowTruncatedOffsetsCleanLoadedSum n offsets x =
      (offsets.map fun offset =>
        if x.1.1.inverseScratch.val.testBit offset.val then
          ((x.1.1.numerator.val * 2 ^ offset.val : Nat) : ProductRowWork n)
        else
          0).sum := by
  induction offsets with
  | nil =>
      rfl
  | cons offset rest ih =>
      simp [productRowTruncatedOffsetsCleanLoadedSum,
        productRowTruncatedCleanLoadedRow_eq_if_shiftedNumerator n offset x,
        ih]

/-- A non-wrapping row slice preserves the clean-loaded-row sum for any future
offset list. -/
theorem productRowTruncatedOffsetsCleanLoadedSum_eq_after_offset
    (n : Nat) (offsets : List (Fin n)) (offset : Fin n)
    (x : PipelineWithProductRowWork n) :
    productRowTruncatedOffsetsCleanLoadedSum n offsets
        (productRowTruncatedOffsetAddStep n offset x) =
      productRowTruncatedOffsetsCleanLoadedSum n offsets x := by
  induction offsets with
  | nil =>
      rfl
  | cons future rest ih =>
      simp [productRowTruncatedOffsetsCleanLoadedSum,
        productRowTruncatedCleanLoadedRow_eq_after_offset n future offset x,
        ih]

/-- Starting from a clean product row, the recursive non-wrapping loaded-row
sum is the clean loaded-row sum read from the initial source pipeline. -/
theorem productRowTruncatedOffsetsLoadedSum_eq_cleanLoadedSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    productRowTruncatedOffsetsLoadedSum n offsets x =
      productRowTruncatedOffsetsCleanLoadedSum n offsets x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      have hrowNext :
          (productRowTruncatedOffsetAddStep n offset x).2 = 0 :=
        productRowTruncatedOffsetAddStep_get_row_clean n offset x hrow
      change
        (productRowTruncatedShiftedLoadStep n offset x).2 +
            productRowTruncatedOffsetsLoadedSum n rest
              (productRowTruncatedOffsetAddStep n offset x) =
          productRowTruncatedCleanLoadedRow n offset x +
            productRowTruncatedOffsetsCleanLoadedSum n rest x
      rw [productRowTruncatedShiftedLoadStep_get_row_clean n offset x hrow]
      rw [ih (productRowTruncatedOffsetAddStep n offset x) hrowNext]
      rw [productRowTruncatedOffsetsCleanLoadedSum_eq_after_offset
        n rest offset x]

/-- Folding any non-wrapping row-slice list preserves inverse-scratch
readouts. -/
theorem productRowTruncatedOffsetsStep_get_inverseScratchBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit bit).get
        (productRowTruncatedOffsetsStep n offsets x) =
      ((productRowWorkspaceInverseScratchWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      exact
        (ih (productRowTruncatedOffsetAddStep n offset x)).trans
          (productRowTruncatedOffsetAddStep_get_inverseScratchBit
            n offset bit x)

/-- Folding any non-wrapping row-slice list preserves numerator readouts. -/
theorem productRowTruncatedOffsetsStep_get_numeratorBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit bit).get
        (productRowTruncatedOffsetsStep n offsets x) =
      ((productRowWorkspaceNumeratorWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      exact
        (ih (productRowTruncatedOffsetAddStep n offset x)).trans
          (productRowTruncatedOffsetAddStep_get_numeratorBit n offset bit x)

/-- Folding any non-wrapping row-slice list preserves target readouts. -/
theorem productRowTruncatedOffsetsStep_get_targetBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit bit).get
        (productRowTruncatedOffsetsStep n offsets x) =
      ((productRowWorkspaceTargetWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      exact
        (ih (productRowTruncatedOffsetAddStep n offset x)).trans
          (productRowTruncatedOffsetAddStep_get_targetBit n offset bit x)

/-- Folding any non-wrapping row-slice list preserves the target field. -/
theorem productRowTruncatedOffsetsStep_get_target
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedOffsetsStep n offsets x).1.1.target =
      x.1.1.target := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceTargetBit_get_testBit n bit
    (productRowTruncatedOffsetsStep n offsets x)]
  rw [productRowTruncatedOffsetsStep_get_targetBit n offsets bit x]
  exact productRowWorkspaceTargetBit_get_testBit n bit x

/-- Folding any non-wrapping row-slice list preserves the denominator. -/
theorem productRowTruncatedOffsetsStep_get_denominator
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    (productRowTruncatedOffsetsStep n offsets x).1.1.denominator =
      x.1.1.denominator := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      exact
        (ih (productRowTruncatedOffsetAddStep n offset x)).trans
          (productRowTruncatedOffsetAddStep_get_denominator n offset x)

/-- Folding any non-wrapping row-slice list preserves the cleanup flag. -/
theorem productRowTruncatedOffsetsStep_get_flagBit
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowTruncatedOffsetsStep n offsets x) =
      (productRowWorkspaceFlagBit n).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      exact
        (ih (productRowTruncatedOffsetAddStep n offset x)).trans
          (productRowTruncatedOffsetAddStep_get_flagBit n offset x)

/-- Folding any non-wrapping row-slice list restores clean temporary carry work
when started from clean carry work. -/
theorem productRowTruncatedOffsetsStep_get_carryWork_clean
    (n : Nat) (offsets : List (Fin n)) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowTruncatedOffsetsStep n offsets x) =
      false := by
  induction offsets generalizing x with
  | nil =>
      exact hwork j
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      apply ih
      intro k
      exact productRowTruncatedOffsetAddStep_get_carryWork_clean
        n offset k x hwork

/-- Folding non-wrapping row slices restores a clean product row. -/
theorem productRowTruncatedOffsetsStep_get_row_clean
    (n : Nat) (offsets : List (Fin n))
    (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowTruncatedOffsetsStep n offsets x).2 = 0 := by
  induction offsets generalizing x with
  | nil =>
      exact hrow
  | cons offset rest ih =>
      rw [productRowTruncatedOffsetsStep]
      apply ih
      exact productRowTruncatedOffsetAddStep_get_row_clean n offset x hrow

/-- Folding non-wrapping row slices adds their concrete filtered loaded-row sum
into quotient scratch. -/
theorem productRowTruncatedOffsetsStep_get_quotientScratch_add_loadedSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowTruncatedOffsetsStep n offsets x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowTruncatedOffsetsLoadedSum n offsets x := by
  induction offsets generalizing x with
  | nil =>
      simp [productRowTruncatedOffsetsStep,
        productRowTruncatedOffsetsLoadedSum]
  | cons offset rest ih =>
      have hflagNext :
          (productRowWorkspaceFlagBit n).get
              (productRowTruncatedOffsetAddStep n offset x) = false := by
        rw [productRowTruncatedOffsetAddStep_get_flagBit]
        exact hflag
      have hworkNext :
          ∀ k : Fin (n - 1),
            ((productRowWorkspaceCarryWorkWord n).bit k).get
                (productRowTruncatedOffsetAddStep n offset x) = false := by
        intro k
        exact productRowTruncatedOffsetAddStep_get_carryWork_clean
          n offset k x hwork
      rw [productRowTruncatedOffsetsStep]
      rw [ih (productRowTruncatedOffsetAddStep n offset x)
        hflagNext hworkNext]
      rw [productRowTruncatedOffsetAddStep_get_quotientScratch_add_loadedRow
        n offset x hflag hwork]
      simp [productRowTruncatedOffsetsLoadedSum, add_assoc]

/-- The non-wrapping folded offset-list program realizes its folded row-slice
semantics on the same filtered gate objects used by each slice. -/
theorem productRowTruncatedOffsets_realizes
    (n : Nat) (offsets : List (Fin n)) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowTruncatedOffsetsProgram n offsets)
      (productRowTruncatedOffsetsStep n offsets) := by
  induction offsets with
  | nil =>
      simpa [productRowTruncatedOffsetsProgram,
        productRowTruncatedOffsetsStep] using
        BaseGateProgram.Realizes.id (pipelineWithProductRowWorkEncoding n)
  | cons offset rest ih =>
      simpa [productRowTruncatedOffsetsProgram,
        productRowTruncatedOffsetsStep] using
        BaseGateProgram.Realizes.append
          (firstStep := productRowTruncatedOffsetAddStep n offset)
          (secondStep := productRowTruncatedOffsetsStep n rest)
          (productRowTruncatedOffsetAdd_realizes n offset) ih

/-- Full non-wrapping product-row program before the remaining arithmetic
endpoint proof: it folds one filtered load/add/unload row slice over every
inverse-scratch bit [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618]. -/
def productRowsTruncatedProgram (n : Nat) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  productRowTruncatedOffsetsProgram n (productRowOffsets n)

/-- Folded semantic action of the full non-wrapping product-row program. -/
def productRowsTruncatedStep (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  productRowTruncatedOffsetsStep n (productRowOffsets n)

/-- The full non-wrapping product-row program preserves inverse-scratch
readouts. -/
theorem productRowsTruncatedStep_get_inverseScratchBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit bit).get
        (productRowsTruncatedStep n x) =
      ((productRowWorkspaceInverseScratchWord n).bit bit).get x := by
  exact productRowTruncatedOffsetsStep_get_inverseScratchBit
    n (productRowOffsets n) bit x

/-- The full non-wrapping product-row program preserves inverse scratch. -/
theorem productRowsTruncatedStep_get_inverseScratch
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsTruncatedStep n x).1.1.inverseScratch =
      x.1.1.inverseScratch := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceInverseScratchBit_get_testBit n bit
    (productRowsTruncatedStep n x)]
  rw [productRowsTruncatedStep_get_inverseScratchBit n bit x]
  exact productRowWorkspaceInverseScratchBit_get_testBit n bit x

/-- The full non-wrapping product-row program preserves numerator readouts. -/
theorem productRowsTruncatedStep_get_numeratorBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit bit).get
        (productRowsTruncatedStep n x) =
      ((productRowWorkspaceNumeratorWord n).bit bit).get x := by
  exact productRowTruncatedOffsetsStep_get_numeratorBit
    n (productRowOffsets n) bit x

/-- The full non-wrapping product-row program preserves the numerator. -/
theorem productRowsTruncatedStep_get_numerator
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsTruncatedStep n x).1.1.numerator = x.1.1.numerator := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceNumeratorBit_get_testBit n bit
    (productRowsTruncatedStep n x)]
  rw [productRowsTruncatedStep_get_numeratorBit n bit x]
  exact productRowWorkspaceNumeratorBit_get_testBit n bit x

/-- The full non-wrapping product-row program preserves target readouts. -/
theorem productRowsTruncatedStep_get_targetBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceTargetWord n).bit bit).get
        (productRowsTruncatedStep n x) =
      ((productRowWorkspaceTargetWord n).bit bit).get x := by
  exact productRowTruncatedOffsetsStep_get_targetBit
    n (productRowOffsets n) bit x

/-- The full non-wrapping product-row program preserves the target field. -/
theorem productRowsTruncatedStep_get_target
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsTruncatedStep n x).1.1.target = x.1.1.target :=
  productRowTruncatedOffsetsStep_get_target n (productRowOffsets n) x

/-- The full non-wrapping product-row program preserves the denominator. -/
theorem productRowsTruncatedStep_get_denominator
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsTruncatedStep n x).1.1.denominator = x.1.1.denominator :=
  productRowTruncatedOffsetsStep_get_denominator n (productRowOffsets n) x

/-- The full non-wrapping product-row program preserves the cleanup flag. -/
theorem productRowsTruncatedStep_get_flagBit
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get (productRowsTruncatedStep n x) =
      (productRowWorkspaceFlagBit n).get x := by
  exact productRowTruncatedOffsetsStep_get_flagBit n (productRowOffsets n) x

/-- The full non-wrapping product-row program preserves the cleanup flag field. -/
theorem productRowsTruncatedStep_get_flag
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsTruncatedStep n x).1.1.flag = x.1.1.flag := by
  simpa using productRowsTruncatedStep_get_flagBit n x

/-- The full non-wrapping product-row program restores clean temporary carry
work when started from clean carry work. -/
theorem productRowsTruncatedStep_get_carryWork_clean
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowsTruncatedStep n x) =
      false := by
  exact productRowTruncatedOffsetsStep_get_carryWork_clean
    n (productRowOffsets n) j x hwork

/-- The full non-wrapping product-row program restores a clean product row. -/
theorem productRowsTruncatedStep_get_row_clean
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    (productRowsTruncatedStep n x).2 = 0 := by
  exact productRowTruncatedOffsetsStep_get_row_clean
    n (productRowOffsets n) x hrow

/-- The full non-wrapping product-row program adds its concrete filtered
loaded-row sum into quotient scratch. -/
theorem productRowsTruncatedStep_get_quotientScratch_add_loadedSum
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsTruncatedStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowTruncatedOffsetsLoadedSum n (productRowOffsets n) x := by
  exact productRowTruncatedOffsetsStep_get_quotientScratch_add_loadedSum
    n (productRowOffsets n) x hflag hwork

/-- The full non-wrapping product-row program, from a clean row, adds the
clean loaded-row sum into quotient scratch. -/
theorem productRowsTruncatedStep_get_quotientScratch_add_cleanLoadedSum
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsTruncatedStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowTruncatedOffsetsCleanLoadedSum n (productRowOffsets n) x := by
  rw [productRowsTruncatedStep_get_quotientScratch_add_loadedSum
    n x hflag hwork]
  rw [productRowTruncatedOffsetsLoadedSum_eq_cleanLoadedSum
    n (productRowOffsets n) x hrow]

/-- Closed form for the full non-wrapping clean loaded-row sum over all
inverse-scratch offsets. -/
theorem productRowsTruncatedCleanLoadedSum_eq_shiftedNumeratorFinSum
    (n : Nat) (x : PipelineWithProductRowWork n) :
    productRowTruncatedOffsetsCleanLoadedSum n (productRowOffsets n) x =
      ∑ offset : Fin n,
        if x.1.1.inverseScratch.val.testBit offset.val then
          ((x.1.1.numerator.val * 2 ^ offset.val : Nat) :
            ProductRowWork n)
        else
          0 := by
  rw [productRowTruncatedOffsetsCleanLoadedSum_eq_shiftedNumeratorListSum]
  simp [productRowOffsets, List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- The full non-wrapping clean loaded-row sum is the low `n`-bit product of
the numerator and inverse scratch. -/
theorem productRowTruncatedOffsetsCleanLoadedSum_eq_mul
    (n : Nat) (x : PipelineWithProductRowWork n) :
    productRowTruncatedOffsetsCleanLoadedSum n (productRowOffsets n) x =
      x.1.1.numerator * x.1.1.inverseScratch := by
  rw [productRowsTruncatedCleanLoadedSum_eq_shiftedNumeratorFinSum]
  exact zmod_twoPow_shiftedBitSum_eq_mul
    n x.1.1.numerator x.1.1.inverseScratch

/-- From a clean row, the concrete loaded-row sum is the low `n`-bit product of
the numerator and inverse scratch. -/
theorem productRowTruncatedOffsetsLoadedSum_eq_mul
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    productRowTruncatedOffsetsLoadedSum n (productRowOffsets n) x =
      x.1.1.numerator * x.1.1.inverseScratch := by
  rw [productRowTruncatedOffsetsLoadedSum_eq_cleanLoadedSum
    n (productRowOffsets n) x hrow]
  exact productRowTruncatedOffsetsCleanLoadedSum_eq_mul n x

/-- The full non-wrapping product-row program, from clean work, adds the actual
low `n`-bit numerator/inverse-scratch product into quotient scratch. -/
theorem productRowsTruncatedStep_get_quotientScratch_add_product
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsTruncatedStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        x.1.1.numerator * x.1.1.inverseScratch := by
  rw [productRowsTruncatedStep_get_quotientScratch_add_cleanLoadedSum
    n x hrow hflag hwork]
  rw [productRowTruncatedOffsetsCleanLoadedSum_eq_mul]

/-- Clean endpoint facts for the full non-wrapping product-row program.  These
are the local facts needed by the product-workspace wrapper: the same gate
object realizes the quotient-scratch product update while preserving the
pipeline source/target fields it should not touch and cleaning temporary row
and carry work [PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350,591-618]. -/
theorem productRowsTruncatedStep_cleanEndpoint
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsTruncatedStep n x).1.1.denominator = x.1.1.denominator ∧
      (productRowsTruncatedStep n x).1.1.numerator = x.1.1.numerator ∧
      (productRowsTruncatedStep n x).1.1.target = x.1.1.target ∧
      (productRowsTruncatedStep n x).1.1.inverseScratch =
        x.1.1.inverseScratch ∧
      (productRowsTruncatedStep n x).1.1.quotientScratch =
        x.1.1.quotientScratch +
          x.1.1.numerator * x.1.1.inverseScratch ∧
      (productRowsTruncatedStep n x).1.1.flag = x.1.1.flag ∧
      (∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get
          (productRowsTruncatedStep n x) = false) ∧
      (productRowsTruncatedStep n x).2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact productRowsTruncatedStep_get_denominator n x
  · exact productRowsTruncatedStep_get_numerator n x
  · exact productRowsTruncatedStep_get_target n x
  · exact productRowsTruncatedStep_get_inverseScratch n x
  · exact productRowsTruncatedStep_get_quotientScratch_add_product
      n x hrow hflag hwork
  · exact productRowsTruncatedStep_get_flag n x
  · intro k
    exact productRowsTruncatedStep_get_carryWork_clean n k x hwork
  · exact productRowsTruncatedStep_get_row_clean n x hrow

/-- State-level clean endpoint for the full non-wrapping product-row program. -/
theorem productRowsTruncatedStep_cleanEndpoint_eq
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    productRowsTruncatedStep n x =
      ((addProductToQuotientScratch x.1.1, cleanWork n), 0) := by
  let y := productRowsTruncatedStep n x
  change y = ((addProductToQuotientScratch x.1.1, cleanWork n), 0)
  have hendpoint :
      y.1.1.denominator = x.1.1.denominator ∧
        y.1.1.numerator = x.1.1.numerator ∧
        y.1.1.target = x.1.1.target ∧
        y.1.1.inverseScratch = x.1.1.inverseScratch ∧
        y.1.1.quotientScratch =
          x.1.1.quotientScratch +
            x.1.1.numerator * x.1.1.inverseScratch ∧
        y.1.1.flag = x.1.1.flag ∧
        (∀ k : Fin (n - 1),
          ((productRowWorkspaceCarryWorkWord n).bit k).get y = false) ∧
        y.2 = 0 := by
    dsimp [y]
    exact productRowsTruncatedStep_cleanEndpoint n x hrow hflag hwork
  rcases hendpoint with
    ⟨hden, hnum, htgt, hinv, hquot, hflg, hwork', hrow'⟩
  have hcarry :
      y.1.2 = cleanWork n :=
    productRowWorkspaceCarryWork_eq_clean_of_get_false
      n y hwork'
  rcases x with ⟨pipeline, row⟩
  rcases pipeline with ⟨s, work⟩
  rcases s with ⟨den, num, tgt, inv, quot, flg⟩
  rcases y with ⟨pipeline', row'⟩
  rcases pipeline' with ⟨s', work'⟩
  rcases s' with ⟨den', num', tgt', inv', quot', flg'⟩
  change den' = den at hden
  change num' = num at hnum
  change tgt' = tgt at htgt
  change inv' = inv at hinv
  change quot' = quot + num * inv at hquot
  change flg' = flg at hflg
  change work' = cleanWork n at hcarry
  change row' = 0 at hrow'
  subst den'
  subst num'
  subst tgt'
  subst inv'
  subst quot'
  subst flg'
  subst work'
  subst row'
  simp [addProductToQuotientScratch]

/-- The full non-wrapping product-row program realizes its folded semantics on
the same filtered base-gate object used for resource accounting. -/
theorem productRowsTruncated_realizes (n : Nat) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowsTruncatedProgram n) (productRowsTruncatedStep n) :=
  productRowTruncatedOffsets_realizes n (productRowOffsets n)

/-- Same-Circuit witness for the full non-wrapping product-row program. -/
def productRowsTruncatedSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowsTruncatedStep n) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowsTruncatedProgram n
  realizes := productRowsTruncated_realizes n

/-- Fold a list of product-row offsets into one base-gate program. -/
def productRowOffsetsProgram (n : Nat) :
    List (Fin n) -> BaseGateProgram (pipelineWithProductRowWorkEncoding n).width
  | [] => []
  | offset :: rest =>
      BaseGateProgram.append (productRowOffsetAddProgram n offset)
        (productRowOffsetsProgram n rest)

/-- Folded semantic action for a list of product-row offsets. -/
def productRowOffsetsStep (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> PipelineWithProductRowWork n
  | [] => id
  | offset :: rest =>
      fun x => productRowOffsetsStep n rest (productRowOffsetAddStep n offset x)

/-- Sum of the concrete rows loaded by a folded offset list, following the same
load/add/unload shifted-product route [PZ03, ecc.tex:622-640]. -/
def productRowOffsetsLoadedSum (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> ProductRowWork n
  | [] => fun _ => 0
  | offset :: rest =>
      fun x =>
        (productRowControlledShiftedLoadStep n offset x).2 +
          productRowOffsetsLoadedSum n rest
            (productRowOffsetAddStep n offset x)

/-- Sum of clean loaded rows, all read from the same source pipeline. -/
def productRowOffsetsCleanLoadedSum (n : Nat) :
    List (Fin n) -> PipelineWithProductRowWork n -> ProductRowWork n
  | [] => fun _ => 0
  | offset :: rest =>
      fun x =>
        productRowCleanLoadedRow n offset x +
          productRowOffsetsCleanLoadedSum n rest x

/-- A row slice preserves the clean-loaded-row sum for any future offset list. -/
theorem productRowOffsetsCleanLoadedSum_eq_after_offset
    (n : Nat) (offsets : List (Fin n)) (offset : Fin n)
    (x : PipelineWithProductRowWork n) :
    productRowOffsetsCleanLoadedSum n offsets
        (productRowOffsetAddStep n offset x) =
      productRowOffsetsCleanLoadedSum n offsets x := by
  induction offsets with
  | nil =>
      rfl
  | cons future rest ih =>
      simp [productRowOffsetsCleanLoadedSum,
        productRowCleanLoadedRow_eq_after_offset n future offset x, ih]

/-- Starting from a clean product row, the recursive loaded-row sum is the clean
loaded-row sum read from the initial source pipeline. -/
theorem productRowOffsetsLoadedSum_eq_cleanLoadedSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0) :
    productRowOffsetsLoadedSum n offsets x =
      productRowOffsetsCleanLoadedSum n offsets x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      have hrowNext :
          (productRowOffsetAddStep n offset x).2 = 0 := by
        rw [productRowOffsetAddStep_get_row]
        exact hrow
      change
        (productRowControlledShiftedLoadStep n offset x).2 +
            productRowOffsetsLoadedSum n rest
              (productRowOffsetAddStep n offset x) =
          productRowCleanLoadedRow n offset x +
            productRowOffsetsCleanLoadedSum n rest x
      rw [productRowControlledShiftedLoadStep_get_row_clean n offset x hrow]
      rw [ih (productRowOffsetAddStep n offset x) hrowNext]
      rw [productRowOffsetsCleanLoadedSum_eq_after_offset n rest offset x]

/-- Folding any list of row slices preserves every product-row bit. -/
theorem productRowOffsetsStep_get_rowBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit bit).get
        (productRowOffsetsStep n offsets x) =
      ((productRowWorkspaceRowWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowOffsetsStep]
      exact
        (ih (productRowOffsetAddStep n offset x)).trans
          (productRowOffsetAddStep_get_rowBit n offset bit x)

/-- Folding any list of row slices preserves the product-row workspace value. -/
theorem productRowOffsetsStep_get_row
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    (productRowOffsetsStep n offsets x).2 = x.2 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro bit
  rw [← productRowWorkspaceRowBit_get_testBit n bit
      (productRowOffsetsStep n offsets x)]
  rw [productRowOffsetsStep_get_rowBit n offsets bit x]
  exact productRowWorkspaceRowBit_get_testBit n bit x

/-- Folding any list of row slices preserves inverse-scratch readouts. -/
theorem productRowOffsetsStep_get_inverseScratchBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit bit).get
        (productRowOffsetsStep n offsets x) =
      ((productRowWorkspaceInverseScratchWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowOffsetsStep]
      exact
        (ih (productRowOffsetAddStep n offset x)).trans
          (productRowOffsetAddStep_get_inverseScratchBit n offset bit x)

/-- Folding any list of row slices preserves numerator readouts. -/
theorem productRowOffsetsStep_get_numeratorBit
    (n : Nat) (offsets : List (Fin n)) (bit : Fin n)
    (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit bit).get
        (productRowOffsetsStep n offsets x) =
      ((productRowWorkspaceNumeratorWord n).bit bit).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowOffsetsStep]
      exact
        (ih (productRowOffsetAddStep n offset x)).trans
          (productRowOffsetAddStep_get_numeratorBit n offset bit x)

/-- Folding any list of row slices preserves the cleanup flag. -/
theorem productRowOffsetsStep_get_flagBit
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get
        (productRowOffsetsStep n offsets x) =
      (productRowWorkspaceFlagBit n).get x := by
  induction offsets generalizing x with
  | nil =>
      rfl
  | cons offset rest ih =>
      rw [productRowOffsetsStep]
      exact
        (ih (productRowOffsetAddStep n offset x)).trans
          (productRowOffsetAddStep_get_flagBit n offset x)

/-- Folding any list of row slices restores clean temporary carry work when
started from clean carry work. -/
theorem productRowOffsetsStep_get_carryWork_clean
    (n : Nat) (offsets : List (Fin n)) (j : Fin (n - 1))
    (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get
        (productRowOffsetsStep n offsets x) =
      false := by
  induction offsets generalizing x with
  | nil =>
      exact hwork j
  | cons offset rest ih =>
      rw [productRowOffsetsStep]
      apply ih
      intro k
      exact productRowOffsetAddStep_get_carryWork_clean n offset k x hwork

/-- Folding row slices adds the concrete loaded rows into quotient scratch. -/
theorem productRowOffsetsStep_get_quotientScratch_add_loadedSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowOffsetsStep n offsets x).1.1.quotientScratch =
      x.1.1.quotientScratch + productRowOffsetsLoadedSum n offsets x := by
  induction offsets generalizing x with
  | nil =>
      simp [productRowOffsetsStep, productRowOffsetsLoadedSum]
  | cons offset rest ih =>
      have hflagNext :
          (productRowWorkspaceFlagBit n).get
              (productRowOffsetAddStep n offset x) = false := by
        rw [productRowOffsetAddStep_get_flagBit]
        exact hflag
      have hworkNext :
          ∀ k : Fin (n - 1),
            ((productRowWorkspaceCarryWorkWord n).bit k).get
                (productRowOffsetAddStep n offset x) = false := by
        intro k
        exact productRowOffsetAddStep_get_carryWork_clean n offset k x hwork
      rw [productRowOffsetsStep]
      rw [ih (productRowOffsetAddStep n offset x) hflagNext hworkNext]
      rw [productRowOffsetAddStep_get_quotientScratch_add_loadedRow
        n offset x hflag hwork]
      simp [productRowOffsetsLoadedSum, add_assoc]

/-- Folding row slices from a clean row adds the clean loaded-row sum into
quotient scratch. -/
theorem productRowOffsetsStep_get_quotientScratch_add_cleanLoadedSum
    (n : Nat) (offsets : List (Fin n)) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowOffsetsStep n offsets x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowOffsetsCleanLoadedSum n offsets x := by
  rw [productRowOffsetsStep_get_quotientScratch_add_loadedSum
    n offsets x hflag hwork]
  rw [productRowOffsetsLoadedSum_eq_cleanLoadedSum n offsets x hrow]

/-- The folded offset-list program realizes its folded row-slice semantics. -/
theorem productRowOffsets_realizes (n : Nat) (offsets : List (Fin n)) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowOffsetsProgram n offsets)
      (productRowOffsetsStep n offsets) := by
  induction offsets with
  | nil =>
      simpa [productRowOffsetsProgram, productRowOffsetsStep] using
        BaseGateProgram.Realizes.id (pipelineWithProductRowWorkEncoding n)
  | cons offset rest ih =>
      simpa [productRowOffsetsProgram, productRowOffsetsStep] using
        BaseGateProgram.Realizes.append
          (firstStep := productRowOffsetAddStep n offset)
          (secondStep := productRowOffsetsStep n rest)
          (productRowOffsetAdd_realizes n offset) ih

/-- Legacy cyclic shifted-row product program: it folds one load/add/unload row
slice over every inverse-scratch bit [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618].  The quotient-product witness below uses the
non-wrapping truncated variant. -/
def productRowsProgram (n : Nat) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  productRowOffsetsProgram n (productRowOffsets n)

/-- Folded semantic action of the full shifted-row product program. -/
def productRowsStep (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  productRowOffsetsStep n (productRowOffsets n)

/-- The full folded product-row program preserves every product-row bit. -/
theorem productRowsStep_get_rowBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceRowWord n).bit bit).get (productRowsStep n x) =
      ((productRowWorkspaceRowWord n).bit bit).get x := by
  exact productRowOffsetsStep_get_rowBit n (productRowOffsets n) bit x

/-- The full folded product-row program preserves the product-row workspace. -/
theorem productRowsStep_get_row
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowsStep n x).2 = x.2 := by
  exact productRowOffsetsStep_get_row n (productRowOffsets n) x

/-- The full folded product-row program preserves inverse-scratch readouts. -/
theorem productRowsStep_get_inverseScratchBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceInverseScratchWord n).bit bit).get
        (productRowsStep n x) =
      ((productRowWorkspaceInverseScratchWord n).bit bit).get x := by
  exact productRowOffsetsStep_get_inverseScratchBit n (productRowOffsets n) bit x

/-- The full folded product-row program preserves numerator readouts. -/
theorem productRowsStep_get_numeratorBit
    (n : Nat) (bit : Fin n) (x : PipelineWithProductRowWork n) :
    ((productRowWorkspaceNumeratorWord n).bit bit).get
        (productRowsStep n x) =
      ((productRowWorkspaceNumeratorWord n).bit bit).get x := by
  exact productRowOffsetsStep_get_numeratorBit n (productRowOffsets n) bit x

/-- The full folded product-row program preserves the cleanup flag. -/
theorem productRowsStep_get_flagBit
    (n : Nat) (x : PipelineWithProductRowWork n) :
    (productRowWorkspaceFlagBit n).get (productRowsStep n x) =
      (productRowWorkspaceFlagBit n).get x := by
  exact productRowOffsetsStep_get_flagBit n (productRowOffsets n) x

/-- The full folded product-row program restores clean temporary carry work
when started from clean carry work. -/
theorem productRowsStep_get_carryWork_clean
    (n : Nat) (j : Fin (n - 1)) (x : PipelineWithProductRowWork n)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowWorkspaceCarryWorkWord n).bit j).get (productRowsStep n x) =
      false := by
  exact productRowOffsetsStep_get_carryWork_clean
    n (productRowOffsets n) j x hwork

/-- The full folded product-row program adds its concrete loaded-row sum into
quotient scratch. -/
theorem productRowsStep_get_quotientScratch_add_loadedSum
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowOffsetsLoadedSum n (productRowOffsets n) x := by
  exact productRowOffsetsStep_get_quotientScratch_add_loadedSum
    n (productRowOffsets n) x hflag hwork

/-- The full folded product-row program, from a clean row, adds the clean
loaded-row sum into quotient scratch. -/
theorem productRowsStep_get_quotientScratch_add_cleanLoadedSum
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsStep n x).1.1.quotientScratch =
      x.1.1.quotientScratch +
        productRowOffsetsCleanLoadedSum n (productRowOffsets n) x := by
  exact productRowOffsetsStep_get_quotientScratch_add_cleanLoadedSum
    n (productRowOffsets n) x hrow hflag hwork

/-- The full shifted-row product program realizes its folded semantics on the
same base-gate object used for resource accounting. -/
theorem productRows_realizes (n : Nat) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      (productRowsProgram n) (productRowsStep n) :=
  productRowOffsets_realizes n (productRowOffsets n)

/-- Same-Circuit witness for the full shifted-row product program. -/
def productRowsSameCircuit (n : Nat) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (productRowsStep n) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := productRowsProgram n
  realizes := productRows_realizes n

/-- Lift the quotient-target-add leg over an explicit product-compute
workspace. -/
def addQuotientToTargetWithProductWork (n : Nat) {ProductWork : Type} :
    PipelineWithProductWork n ProductWork ->
      PipelineWithProductWork n ProductWork
  | (pipeline, productWork) =>
      (addQuotientToTargetWithWork n pipeline, productWork)

/-- Same-Circuit target-add witness over a product-compute workspace. -/
def pipelineWithProductWorkTargetAddSameCircuit (n : Nat)
    {ProductWork : Type} (productEncoding : BinaryLabelEncoding ProductWork) :
    BaseGateSameCircuitWitness (PipelineWithProductWork n ProductWork)
      (addQuotientToTargetWithProductWork n) :=
  BaseGateSameCircuitWitness.prodLeft (pipelineWithWorkSameCircuit n)
    productEncoding

/-- Product-compute / target-add / inverse-product schedule over explicit
product workspace. The product compute may dirty this workspace, but the
inverse folded program must clean it through the supplied semantic inverse
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
def reversibleProductStepWithWorkspace (n : Nat) {ProductWork : Type}
    (productStep unproductStep :
      PipelineWithProductWork n ProductWork ->
        PipelineWithProductWork n ProductWork) :
    PipelineWithProductWork n ProductWork ->
      PipelineWithProductWork n ProductWork :=
  fun x =>
    unproductStep
      (addQuotientToTargetWithProductWork n (productStep x))

/-- Decomposed quotient-product witness over explicit product-compute
workspace. This is the honest plug-in point for the quotient-product theorem
route: it records the same base-gate program used for product correctness and
resource accounting, and `productRowsDecomposedWitness` below instantiates it
with the non-wrapping controlled shifted-add product program [PZ03,
ecc.tex:622-640]. -/
structure DecomposedProductWithWorkspaceWitness (n : Nat)
    {ProductWork : Type} (productEncoding : BinaryLabelEncoding ProductWork) where
  /-- Semantic action of the quotient-product compute program. -/
  productStep :
    PipelineWithProductWork n ProductWork ->
      PipelineWithProductWork n ProductWork
  /-- Semantic action used by the reversed product-compute program. -/
  unproductStep :
    PipelineWithProductWork n ProductWork ->
      PipelineWithProductWork n ProductWork
  /-- Program for the quotient-product compute leg over the full workspace. -/
  productProgram :
    BaseGateProgram (pipelineWithProductWorkEncoding n productEncoding).width
  /-- Correctness of the product-compute program on full workspace labels. -/
  productRealizes :
    BaseGateProgram.Realizes (pipelineWithProductWorkEncoding n productEncoding)
      productProgram productStep
  /-- The supplied unproduct semantic action is a right inverse of product. -/
  product_rightInverse : ∀ x, productStep (unproductStep x) = x

namespace DecomposedProductWithWorkspaceWitness

/-- The semantic update selected by a product-workspace witness. -/
def step {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    PipelineWithProductWork n ProductWork ->
      PipelineWithProductWork n ProductWork :=
  reversibleProductStepWithWorkspace n w.productStep w.unproductStep

/-- Product compute, target-add, and reverse-product as one base-gate program. -/
def program {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    BaseGateProgram (pipelineWithProductWorkEncoding n productEncoding).width :=
  BaseGateProgram.append w.productProgram
    (BaseGateProgram.append
      (pipelineWithProductWorkTargetAddSameCircuit n productEncoding).program
      (BaseGateProgram.inverse w.productProgram))

/-- The decomposed product-workspace program realizes the selected
product/add/unproduct semantic update. -/
theorem realizes {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    BaseGateProgram.Realizes (pipelineWithProductWorkEncoding n productEncoding)
      w.program w.step := by
  have htarget :
      BaseGateProgram.Realizes
        (pipelineWithProductWorkEncoding n productEncoding)
        (pipelineWithProductWorkTargetAddSameCircuit n productEncoding).program
        (addQuotientToTargetWithProductWork n) := by
    simpa [pipelineWithProductWorkEncoding,
      pipelineWithProductWorkTargetAddSameCircuit]
      using
        (pipelineWithProductWorkTargetAddSameCircuit n productEncoding).realizes
  have hunproduct :
      BaseGateProgram.Realizes
        (pipelineWithProductWorkEncoding n productEncoding)
        (BaseGateProgram.inverse w.productProgram) w.unproductStep :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.productRealizes
      w.product_rightInverse
  have htail :
      BaseGateProgram.Realizes
        (pipelineWithProductWorkEncoding n productEncoding)
        (BaseGateProgram.append
          (pipelineWithProductWorkTargetAddSameCircuit n productEncoding).program
          (BaseGateProgram.inverse w.productProgram))
        (fun x : PipelineWithProductWork n ProductWork =>
          w.unproductStep (addQuotientToTargetWithProductWork n x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := addQuotientToTargetWithProductWork n)
      (secondStep := w.unproductStep)
      htarget hunproduct
  have hfull :
      BaseGateProgram.Realizes
        (pipelineWithProductWorkEncoding n productEncoding)
        w.program w.step :=
    BaseGateProgram.Realizes.append
      (firstStep := w.productStep)
      (secondStep := fun x : PipelineWithProductWork n ProductWork =>
        w.unproductStep (addQuotientToTargetWithProductWork n x))
      w.productRealizes htail
  simpa [program, step, reversibleProductStepWithWorkspace] using hfull

/-- Same-Circuit witness induced by the product-workspace decomposed program. -/
def baseWitness {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    BaseGateSameCircuitWitness (PipelineWithProductWork n ProductWork)
      w.step where
  encoding := pipelineWithProductWorkEncoding n productEncoding
  program := w.program
  realizes := w.realizes

/-- The product-workspace circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for product-workspace labels. -/
theorem apply_ket {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding)
    (x : PipelineWithProductWork n ProductWork) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (pipelineWithProductWorkEncoding n productEncoding).width)
          ((pipelineWithProductWorkEncoding n productEncoding).encode x) :
          PureState
            (Qubits (pipelineWithProductWorkEncoding n productEncoding).width)) :
          StateVector
            (Qubits (pipelineWithProductWorkEncoding n productEncoding).width)) =
      (PureState.ket
        (R := Qubits (pipelineWithProductWorkEncoding n productEncoding).width)
        ((pipelineWithProductWorkEncoding n productEncoding).encode (w.step x)) :
        StateVector
          (Qubits (pipelineWithProductWorkEncoding n productEncoding).width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Resource counters are projected from the same product-workspace circuit. -/
theorem resources_eq {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same product-workspace circuit. -/
theorem depth_eq {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same product-workspace circuit. -/
theorem queryDepth_eq {n : Nat} {ProductWork : Type}
    {productEncoding : BinaryLabelEncoding ProductWork}
    (w : DecomposedProductWithWorkspaceWitness n productEncoding) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

end DecomposedProductWithWorkspaceWitness

/-- Semantic inverse chosen for the legacy cyclic shifted-row product program.
The quotient-product witness below uses the non-wrapping truncated inverse
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350]. -/
noncomputable def productRowsUnstep (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  Function.invFun (productRowsStep n)

/-- The folded shifted-row product semantics is surjective because the same
base-gate program that realizes it is reversible on encoded labels. -/
theorem productRowsStep_surjective (n : Nat) :
    Function.Surjective (productRowsStep n) :=
  Finite.surjective_of_injective
    (BaseGateProgram.Realizes.injective (productRows_realizes n))

/-- The selected semantic inverse is a right inverse for the folded shifted-row
product semantics. -/
theorem productRows_rightInverse (n : Nat) :
    ∀ x, productRowsStep n (productRowsUnstep n x) = x :=
  Function.rightInverse_invFun (productRowsStep_surjective n)

/-- Semantic inverse chosen for the folded non-wrapping product-row program. -/
noncomputable def productRowsTruncatedUnstep (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  Function.invFun (productRowsTruncatedStep n)

/-- The folded non-wrapping product-row semantics is surjective because the
same filtered base-gate program that realizes it is reversible on encoded
labels. -/
theorem productRowsTruncatedStep_surjective (n : Nat) :
    Function.Surjective (productRowsTruncatedStep n) :=
  Finite.surjective_of_injective
    (BaseGateProgram.Realizes.injective (productRowsTruncated_realizes n))

/-- The selected semantic inverse is a right inverse for the folded
non-wrapping product-row semantics. -/
theorem productRowsTruncated_rightInverse (n : Nat) :
    ∀ x, productRowsTruncatedStep n (productRowsTruncatedUnstep n x) = x :=
  Function.rightInverse_invFun (productRowsTruncatedStep_surjective n)

/-- The selected semantic inverse for the folded non-wrapping product-row
program is also a left inverse on product-step outputs. -/
theorem productRowsTruncated_leftInverse_on_range (n : Nat) :
    ∀ x, productRowsTruncatedUnstep n (productRowsTruncatedStep n x) = x := by
  intro x
  apply BaseGateProgram.Realizes.injective (productRowsTruncated_realizes n)
  rw [productRowsTruncated_rightInverse n]

/-- Product-workspace witness obtained from the concrete folded shifted-row
base-gate program.  The integrated witness uses the non-wrapping filtered
product-row path characterized by
`productRowsTruncatedStep_get_quotientScratch_add_product` [PZ03,
ecc.tex:622-640]. -/
noncomputable def productRowsDecomposedWitness (n : Nat) :
    DecomposedProductWithWorkspaceWitness n (productRowEncoding n) where
  productStep := productRowsTruncatedStep n
  unproductStep := productRowsTruncatedUnstep n
  productProgram := productRowsTruncatedProgram n
  productRealizes := productRowsTruncated_realizes n
  product_rightInverse := productRowsTruncated_rightInverse n

/-- Clean endpoint facts exposed through the concrete product-workspace witness.
This is the review handle for the product-workspace compute leg: the witness's
own `productProgram` realizes the product step whose clean endpoint is
summarized here [PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350,591-618]. -/
theorem productRowsDecomposedWitness_product_cleanEndpoint
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    ((productRowsDecomposedWitness n).productStep x).1.1.denominator =
        x.1.1.denominator ∧
      ((productRowsDecomposedWitness n).productStep x).1.1.numerator =
        x.1.1.numerator ∧
      ((productRowsDecomposedWitness n).productStep x).1.1.target =
        x.1.1.target ∧
      ((productRowsDecomposedWitness n).productStep x).1.1.inverseScratch =
        x.1.1.inverseScratch ∧
      ((productRowsDecomposedWitness n).productStep x).1.1.quotientScratch =
        x.1.1.quotientScratch +
          x.1.1.numerator * x.1.1.inverseScratch ∧
      ((productRowsDecomposedWitness n).productStep x).1.1.flag =
        x.1.1.flag ∧
      (∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get
          ((productRowsDecomposedWitness n).productStep x) = false) ∧
      ((productRowsDecomposedWitness n).productStep x).2 = 0 := by
  simpa [productRowsDecomposedWitness] using
    productRowsTruncatedStep_cleanEndpoint n x hrow hflag hwork

/-- State-level clean endpoint exposed through the concrete product-workspace
witness.  This is the quotient-product compute leg as an equality of the same
labels used by the gate program [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618]. -/
theorem productRowsDecomposedWitness_product_cleanEndpoint_eq
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsDecomposedWitness n).productStep x =
      ((addProductToQuotientScratch x.1.1, cleanWork n), 0) := by
  simpa [productRowsDecomposedWitness] using
    productRowsTruncatedStep_cleanEndpoint_eq n x hrow hflag hwork

/-- Clean pipeline endpoint for the work-aware target-add leg. -/
theorem addQuotientToTargetWithWork_cleanEndpoint
    (n : Nat) (s : PipelineState (2 ^ n)) (hflag : s.flag = false) :
    addQuotientToTargetWithWork n (s, cleanWork n) =
      (addQuotientToTarget s, cleanWork n) := by
  have htupleFlag :
      ((tupleEquiv (2 ^ n)) s).2.2.2.2.2 = false := by
    cases s
    simpa [tupleEquiv] using hflag
  have htuple :=
    tupleAddQuotientToTargetWithWork_cleanEndpoint n
      ((tupleEquiv (2 ^ n)) s) htupleFlag
  change
    (let y :=
      tupleAddQuotientToTargetWithWork n
        ((tupleEquiv (2 ^ n)) s, cleanWork n);
      ((tupleEquiv (2 ^ n)).symm y.1, y.2)) =
      (addQuotientToTarget s, cleanWork n)
  rw [htuple]
  simp [tupleAddQuotientToTarget_toPipeline]

/-- Clean endpoint for the target-add leg lifted over the concrete product-row
workspace [PZ03, ecc.tex:622-640; VBE95, 9511018.tex:237-264,591-618]. -/
theorem addQuotientToTargetWithProductRowWork_cleanEndpoint
    (n : Nat) (s : PipelineState (2 ^ n)) (hflag : s.flag = false) :
    addQuotientToTargetWithProductWork n
        ((s, cleanWork n), (0 : ProductRowWork n)) =
      ((addQuotientToTarget s, cleanWork n), 0) := by
  rw [addQuotientToTargetWithProductWork]
  rw [addQuotientToTargetWithWork_cleanEndpoint n s hflag]

/-- Clean endpoint for the concrete product-row compute/target-add/uncompute
segment.  The same product-row gate program computes the quotient product,
the lifted target-add consumes it, and the inverse product-row program restores
the product row and carry workspace [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618]. -/
theorem productRowsDecomposedWitness_cleanEndpoint_eq
    (n : Nat) (x : PipelineWithProductRowWork n)
    (hrow : x.2 = 0)
    (hflag : (productRowWorkspaceFlagBit n).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false) :
    (productRowsDecomposedWitness n).step x =
      ((subProductFromQuotientScratch
          (addQuotientToTarget (addProductToQuotientScratch x.1.1)),
        cleanWork n), 0) := by
  let c : PipelineWithProductRowWork n :=
    ((subProductFromQuotientScratch
        (addQuotientToTarget (addProductToQuotientScratch x.1.1)),
      cleanWork n), 0)
  have hxProduct :
      productRowsTruncatedStep n x =
        ((addProductToQuotientScratch x.1.1, cleanWork n), 0) :=
    productRowsTruncatedStep_cleanEndpoint_eq n x hrow hflag hwork
  have hproductFlag :
      (addProductToQuotientScratch x.1.1).flag = false := by
    simpa [addProductToQuotientScratch] using hflag
  have htarget :
      addQuotientToTargetWithProductWork n (productRowsTruncatedStep n x) =
        ((addQuotientToTarget (addProductToQuotientScratch x.1.1),
          cleanWork n), 0) := by
    rw [hxProduct]
    exact addQuotientToTargetWithProductRowWork_cleanEndpoint
      n (addProductToQuotientScratch x.1.1) hproductFlag
  have hcFlag : (productRowWorkspaceFlagBit n).get c = false := by
    simpa [c, addProductToQuotientScratch, addQuotientToTarget,
      subProductFromQuotientScratch] using hflag
  have hcWork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get c = false := by
    intro k
    exact productRowWorkspaceCarryWorkBit_get_clean n k
      (subProductFromQuotientScratch
        (addQuotientToTarget (addProductToQuotientScratch x.1.1)))
      0
  have hcProduct :
      productRowsTruncatedStep n c =
        ((addQuotientToTarget (addProductToQuotientScratch x.1.1),
          cleanWork n), 0) := by
    have h :=
      productRowsTruncatedStep_cleanEndpoint_eq n c rfl hcFlag hcWork
    simpa [c] using h
  change
    productRowsTruncatedUnstep n
      (addQuotientToTargetWithProductWork n
        (productRowsTruncatedStep n x)) = c
  rw [htarget, ← hcProduct]
  exact productRowsTruncated_leftInverse_on_range n c

/-- Compute the denominator inverse scratch while preserving target-add carry
work. -/
def addInverseToScratchWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n
  | (s, work) => (addInverseToScratch s, work)

/-- Reverse inverse-scratch computation while preserving carry work. -/
def subInverseFromScratchWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n
  | (s, work) => (subInverseFromScratch s, work)

/-- Compute the quotient scratch while preserving target-add carry work. -/
def addProductToQuotientScratchWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n
  | (s, work) => (addProductToQuotientScratch s, work)

/-- Reverse quotient-scratch computation while preserving carry work. -/
def subProductFromQuotientScratchWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n
  | (s, work) => (subProductFromQuotientScratch s, work)

@[simp] theorem addInverseToScratchWithWork_subInverseFromScratchWithWork
    (n : Nat) (x : PipelineWithWork n) :
    addInverseToScratchWithWork n (subInverseFromScratchWithWork n x) = x := by
  rcases x with ⟨s, work⟩
  simp [addInverseToScratchWithWork, subInverseFromScratchWithWork]

@[simp] theorem addProductToQuotientScratchWithWork_subProductFromQuotientScratchWithWork
    (n : Nat) (x : PipelineWithWork n) :
    addProductToQuotientScratchWithWork n
      (subProductFromQuotientScratchWithWork n x) = x := by
  rcases x with ⟨s, work⟩
  simp [addProductToQuotientScratchWithWork,
    subProductFromQuotientScratchWithWork]

/-- Work-aware reversible division pipeline:
inverse compute, quotient-product compute, target-add through the explicit VBE
carry-work bridge, then reverse product and inverse computation [PZ03,
ecc.tex:622-640; VBE95, 9511018.tex:237-264,591-618]. -/
def reversiblePipelineStepWithWork (n : Nat) :
    PipelineWithWork n -> PipelineWithWork n :=
  fun x =>
    subInverseFromScratchWithWork n
      (subProductFromQuotientScratchWithWork n
        (addQuotientToTargetWithWork n
          (addProductToQuotientScratchWithWork n
            (addInverseToScratchWithWork n x))))

/-- The work-aware decomposed pipeline agrees with the clean public division
action when scratch, flag, and carry work start clean. -/
theorem reversiblePipelineStepWithWork_initial
    (n : Nat) (u : (ZMod (2 ^ n))ˣ) (v z : ZMod (2 ^ n)) :
    reversiblePipelineStepWithWork n (initial u v z, cleanWork n) =
      (({ denominator := u
          numerator := v
          target := z + quotientResidue u v
          inverseScratch := 0
          quotientScratch := 0
          flag := false } : PipelineState (2 ^ n)),
        cleanWork n) := by
  unfold reversiblePipelineStepWithWork addInverseToScratchWithWork
    addProductToQuotientScratchWithWork subProductFromQuotientScratchWithWork
    subInverseFromScratchWithWork
  rw [addQuotientToTargetWithWork_cleanEndpoint n
    (addProductToQuotientScratch (addInverseToScratch (initial u v z)))]
  · simp [initial, addInverseToScratch, addProductToQuotientScratch,
      addQuotientToTarget, subProductFromQuotientScratch,
      subInverseFromScratch, quotientResidue]
  · simp [initial, addInverseToScratch, addProductToQuotientScratch]

/-! #### Product-row-aware division wrapper -/

/-- Clean output label for the product-row-aware division wrapper. -/
def cleanProductRowOutput (n : Nat)
    (u : (ZMod (2 ^ n))ˣ) (v z : ZMod (2 ^ n)) :
    PipelineWithProductRowWork n :=
  let s : PipelineState (2 ^ n) :=
    { denominator := u
      numerator := v
      target := z + quotientResidue u v
      inverseScratch := 0
      quotientScratch := 0
      flag := false }
  ((s, cleanWork n), 0)

/-- Compute the denominator inverse scratch while preserving the target-add
carry work and the explicit product-row workspace. -/
def addInverseToScratchWithProductRowWork (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n
  | (pipeline, row) => (addInverseToScratchWithWork n pipeline, row)

/-- Reverse inverse-scratch computation while preserving the target-add carry
work and the explicit product-row workspace. -/
def subInverseFromScratchWithProductRowWork (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n
  | (pipeline, row) => (subInverseFromScratchWithWork n pipeline, row)

@[simp] theorem addInverseToScratchWithProductRowWork_subInverse
    (n : Nat) (x : PipelineWithProductRowWork n) :
    addInverseToScratchWithProductRowWork n
      (subInverseFromScratchWithProductRowWork n x) = x := by
  rcases x with ⟨pipeline, row⟩
  simp [addInverseToScratchWithProductRowWork,
    subInverseFromScratchWithProductRowWork]

/-- Product-row-aware reversible division pipeline: inverse compute, concrete
quotient-product compute/target-add/uncompute, then reverse inverse compute
[PZ03, ecc.tex:622-640; VBE95, 9511018.tex:333-350,591-618]. -/
def reversiblePipelineStepWithProductRowWork (n : Nat) :
    PipelineWithProductRowWork n -> PipelineWithProductRowWork n :=
  fun x =>
    subInverseFromScratchWithProductRowWork n
      ((productRowsDecomposedWitness n).step
        (addInverseToScratchWithProductRowWork n x))

/-- The product-row-aware decomposed pipeline agrees with the clean public
division action when scratch, flag, carry work, and product row start clean. -/
theorem reversiblePipelineStepWithProductRowWork_initial
    (n : Nat) (u : (ZMod (2 ^ n))ˣ) (v z : ZMod (2 ^ n)) :
    reversiblePipelineStepWithProductRowWork n
        ((initial u v z, cleanWork n), (0 : ProductRowWork n)) =
      cleanProductRowOutput n u v z := by
  let x : PipelineWithProductRowWork n :=
    addInverseToScratchWithProductRowWork n
      ((initial u v z, cleanWork n), (0 : ProductRowWork n))
  have hrow : x.2 = 0 := by
    simp [x, addInverseToScratchWithProductRowWork]
  have hflag : (productRowWorkspaceFlagBit n).get x = false := by
    simp [x, addInverseToScratchWithProductRowWork,
      addInverseToScratchWithWork, addInverseToScratch, initial]
  have hwork :
      ∀ k : Fin (n - 1),
        ((productRowWorkspaceCarryWorkWord n).bit k).get x = false := by
    intro k
    simpa [x, addInverseToScratchWithProductRowWork,
      addInverseToScratchWithWork] using
      productRowWorkspaceCarryWorkBit_get_clean n k
        (addInverseToScratch (initial u v z)) (0 : ProductRowWork n)
  have hproduct :=
    productRowsDecomposedWitness_cleanEndpoint_eq n x hrow hflag hwork
  change
    subInverseFromScratchWithProductRowWork n
      ((productRowsDecomposedWitness n).step x) =
      cleanProductRowOutput n u v z
  rw [hproduct]
  simp [x, addInverseToScratchWithProductRowWork,
    subInverseFromScratchWithProductRowWork, addInverseToScratchWithWork,
    subInverseFromScratchWithWork, initial, addInverseToScratch,
    addProductToQuotientScratch, addQuotientToTarget,
    subProductFromQuotientScratch, subInverseFromScratch, quotientResidue,
    cleanProductRowOutput]

/-- Product-row-aware division pipeline witness with a concrete quotient-product
leg.  The inverse leg remains supplied externally by the inverse-compute
blocker, while multiplication/target-add/uncompute are fixed to the
gate-structured product-row witness [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:333-350,591-618]. -/
structure DecomposedPipelineWithProductRowWitness (n : Nat) where
  /-- Program adding the denominator inverse into inverse scratch over the
  product-row-aware layout. -/
  inverseProgram : BaseGateProgram (pipelineWithProductRowWorkEncoding n).width
  /-- Correctness of inverse computation on product-row-aware labels. -/
  inverseRealizes :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
      inverseProgram (addInverseToScratchWithProductRowWork n)

namespace DecomposedPipelineWithProductRowWitness

/-- Inverse, concrete product-row product/target-add/unproduct, and
reverse-inverse as one base-gate program. -/
def program {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    BaseGateProgram (pipelineWithProductRowWorkEncoding n).width :=
  BaseGateProgram.append w.inverseProgram
    (BaseGateProgram.append (productRowsDecomposedWitness n).program
      (BaseGateProgram.inverse w.inverseProgram))

/-- The product-row-aware decomposed program realizes the reversible division
pipeline selected above. -/
theorem realizes {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n) w.program
      (reversiblePipelineStepWithProductRowWork n) := by
  have hproduct :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (productRowsDecomposedWitness n).program
        (productRowsDecomposedWitness n).step := by
    simpa [PipelineWithProductRowWork, pipelineWithProductRowWorkEncoding] using
      (productRowsDecomposedWitness n).realizes
  have huninverse :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (BaseGateProgram.inverse w.inverseProgram)
        (subInverseFromScratchWithProductRowWork n) :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.inverseRealizes
      (addInverseToScratchWithProductRowWork_subInverse n)
  have htail :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n)
        (BaseGateProgram.append (productRowsDecomposedWitness n).program
          (BaseGateProgram.inverse w.inverseProgram))
        (fun x : PipelineWithProductRowWork n =>
          subInverseFromScratchWithProductRowWork n
            ((productRowsDecomposedWitness n).step x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := (productRowsDecomposedWitness n).step)
      (secondStep := subInverseFromScratchWithProductRowWork n)
      hproduct huninverse
  have hfull :
      BaseGateProgram.Realizes (pipelineWithProductRowWorkEncoding n) w.program
        (reversiblePipelineStepWithProductRowWork n) :=
    BaseGateProgram.Realizes.append
      (firstStep := addInverseToScratchWithProductRowWork n)
      (secondStep := fun x : PipelineWithProductRowWork n =>
        subInverseFromScratchWithProductRowWork n
          ((productRowsDecomposedWitness n).step x))
      w.inverseRealizes htail
  simpa [program, reversiblePipelineStepWithProductRowWork] using hfull

/-- Same-Circuit witness induced by the product-row-aware decomposed division
pipeline. -/
def baseWitness {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    BaseGateSameCircuitWitness (PipelineWithProductRowWork n)
      (reversiblePipelineStepWithProductRowWork n) where
  encoding := pipelineWithProductRowWorkEncoding n
  program := w.program
  realizes := w.realizes

/-- The product-row-aware decomposed division circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all product-row-aware division labels. -/
theorem apply_ket {n : Nat}
    (w : DecomposedPipelineWithProductRowWitness n)
    (x : PipelineWithProductRowWork n) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
          ((pipelineWithProductRowWorkEncoding n).encode x) :
          PureState (Qubits (pipelineWithProductRowWorkEncoding n).width)) :
          StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)) =
      (PureState.ket
        (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
        ((pipelineWithProductRowWorkEncoding n).encode
          (reversiblePipelineStepWithProductRowWork n x)) :
        StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Clean encoded-basis action for the product-row-aware decomposed division
wrapper. -/
theorem apply_clean_ket {n : Nat}
    (w : DecomposedPipelineWithProductRowWitness n)
    (u : (ZMod (2 ^ n))ˣ) (v z : ZMod (2 ^ n)) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
          ((pipelineWithProductRowWorkEncoding n).encode
            ((initial u v z, cleanWork n), (0 : ProductRowWork n))) :
          PureState (Qubits (pipelineWithProductRowWorkEncoding n).width)) :
          StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)) =
      (PureState.ket
        (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
        ((pipelineWithProductRowWorkEncoding n).encode
          (cleanProductRowOutput n u v z)) :
        StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)) := by
  simpa [baseWitness, reversiblePipelineStepWithProductRowWork_initial] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness
      ((initial u v z, cleanWork n), (0 : ProductRowWork n))

/-- Resource counters are projected from the same product-row-aware decomposed
division circuit. -/
theorem resources_eq {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same product-row-aware decomposed
division circuit. -/
theorem depth_eq {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same product-row-aware decomposed division
circuit. -/
theorem queryDepth_eq {n : Nat} (w : DecomposedPipelineWithProductRowWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for the clean product-row-aware division pipeline,
conditional only on the supplied inverse-compute subprogram; the quotient
product/target-add/unproduct leg is the concrete product-row witness [PZ03,
ecc.tex:622-640; VBE95, 9511018.tex:333-350,591-618]. -/
def cleanResourceCorrectWitness {n : Nat}
    (w : DecomposedPipelineWithProductRowWitness n) :
    ResourceCorrectWitness
      (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
      (∀ u : (ZMod (2 ^ n))ˣ, ∀ v z : ZMod (2 ^ n),
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket
            (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
            ((pipelineWithProductRowWorkEncoding n).encode
              ((initial u v z, cleanWork n), (0 : ProductRowWork n))) :
            PureState (Qubits (pipelineWithProductRowWorkEncoding n).width)) :
            StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)) =
          (PureState.ket
            (R := Qubits (pipelineWithProductRowWorkEncoding n).width)
            ((pipelineWithProductRowWorkEncoding n).encode
              (cleanProductRowOutput n u v z)) :
            StateVector (Qubits (pipelineWithProductRowWorkEncoding n).width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u v z => apply_clean_ket w u v z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedPipelineWithProductRowWitness

/-- Decomposed division pipeline witness with explicit VBE target-add carry
work.  The target-add-with-aux leg is fixed to `pipelineWithWorkSameCircuit`;
a closing proof must still provide inverse and quotient-product compute
programs under the same pipeline/work encoding [PZ03, ecc.tex:622-640]. -/
structure DecomposedPipelineWithTargetAddWitness (n : Nat) where
  /-- Program adding the denominator inverse into inverse scratch. -/
  inverseProgram :
    BaseGateProgram (pipelineWithWorkSameCircuit n).encoding.width
  /-- Program adding the numerator-inverse product into quotient scratch. -/
  productProgram :
    BaseGateProgram (pipelineWithWorkSameCircuit n).encoding.width
  /-- Correctness of inverse computation on pipeline/work labels. -/
  inverseRealizes :
    BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
      inverseProgram (addInverseToScratchWithWork n)
  /-- Correctness of quotient-product computation on pipeline/work labels. -/
  productRealizes :
    BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
      productProgram (addProductToQuotientScratchWithWork n)

namespace DecomposedPipelineWithTargetAddWitness

/-- Inverse, product, work-aware target-add, reverse-product, and
reverse-inverse as one base-gate program. -/
def program {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    BaseGateProgram (pipelineWithWorkSameCircuit n).encoding.width :=
  BaseGateProgram.append w.inverseProgram
    (BaseGateProgram.append w.productProgram
      (BaseGateProgram.append (pipelineWithWorkSameCircuit n).program
        (BaseGateProgram.append
          (BaseGateProgram.inverse w.productProgram)
          (BaseGateProgram.inverse w.inverseProgram))))

/-- The decomposed work-aware program realizes the reversible division pipeline
with explicit carry work. -/
theorem realizes {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding w.program
      (reversiblePipelineStepWithWork n) := by
  have hunproduct :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
        (BaseGateProgram.inverse w.productProgram)
        (subProductFromQuotientScratchWithWork n) :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.productRealizes
      (addProductToQuotientScratchWithWork_subProductFromQuotientScratchWithWork n)
  have huninverse :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
        (BaseGateProgram.inverse w.inverseProgram)
        (subInverseFromScratchWithWork n) :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.inverseRealizes
      (addInverseToScratchWithWork_subInverseFromScratchWithWork n)
  have hcleanup :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
        (BaseGateProgram.append
          (BaseGateProgram.inverse w.productProgram)
          (BaseGateProgram.inverse w.inverseProgram))
        (fun x : PipelineWithWork n =>
          subInverseFromScratchWithWork n
            (subProductFromQuotientScratchWithWork n x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := subProductFromQuotientScratchWithWork n)
      (secondStep := subInverseFromScratchWithWork n)
      hunproduct huninverse
  have htargetTail :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
        (BaseGateProgram.append (pipelineWithWorkSameCircuit n).program
          (BaseGateProgram.append
            (BaseGateProgram.inverse w.productProgram)
            (BaseGateProgram.inverse w.inverseProgram)))
        (fun x : PipelineWithWork n =>
          subInverseFromScratchWithWork n
            (subProductFromQuotientScratchWithWork n
              (addQuotientToTargetWithWork n x))) :=
    BaseGateProgram.Realizes.append
      (firstStep := addQuotientToTargetWithWork n)
      (secondStep := fun x : PipelineWithWork n =>
        subInverseFromScratchWithWork n
          (subProductFromQuotientScratchWithWork n x))
      (pipelineWithWorkSameCircuit n).realizes hcleanup
  have hproductTail :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding
        (BaseGateProgram.append w.productProgram
          (BaseGateProgram.append (pipelineWithWorkSameCircuit n).program
            (BaseGateProgram.append
              (BaseGateProgram.inverse w.productProgram)
              (BaseGateProgram.inverse w.inverseProgram))))
        (fun x : PipelineWithWork n =>
          subInverseFromScratchWithWork n
            (subProductFromQuotientScratchWithWork n
              (addQuotientToTargetWithWork n
                (addProductToQuotientScratchWithWork n x)))) :=
    BaseGateProgram.Realizes.append
      (firstStep := addProductToQuotientScratchWithWork n)
      (secondStep := fun x : PipelineWithWork n =>
        subInverseFromScratchWithWork n
          (subProductFromQuotientScratchWithWork n
            (addQuotientToTargetWithWork n x)))
      w.productRealizes htargetTail
  have hfull :
      BaseGateProgram.Realizes (pipelineWithWorkSameCircuit n).encoding w.program
        (reversiblePipelineStepWithWork n) :=
    BaseGateProgram.Realizes.append
      (firstStep := addInverseToScratchWithWork n)
      (secondStep := fun x : PipelineWithWork n =>
        subInverseFromScratchWithWork n
          (subProductFromQuotientScratchWithWork n
            (addQuotientToTargetWithWork n
              (addProductToQuotientScratchWithWork n x))))
      w.inverseRealizes hproductTail
  simpa [program, reversiblePipelineStepWithWork] using hfull

/-- Same-Circuit witness induced by the work-aware decomposed division
pipeline. -/
def baseWitness {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    BaseGateSameCircuitWitness (PipelineWithWork n)
      (reversiblePipelineStepWithWork n) where
  encoding := (pipelineWithWorkSameCircuit n).encoding
  program := w.program
  realizes := w.realizes

/-- The work-aware decomposed division circuit history bottoms out in
X/CNOT/Toffoli atoms. -/
theorem structured {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all work-aware division pipeline labels. -/
theorem apply_ket {n : Nat}
    (w : DecomposedPipelineWithTargetAddWitness n) (x : PipelineWithWork n) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
          ((pipelineWithWorkSameCircuit n).encoding.encode x) :
          PureState (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) :
          StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) =
      (PureState.ket
        (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
        ((pipelineWithWorkSameCircuit n).encoding.encode
          (reversiblePipelineStepWithWork n x)) :
        StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) := by
  simpa [baseWitness] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Clean encoded-basis action for the work-aware decomposed division wrapper. -/
theorem apply_clean_ket {n : Nat}
    (w : DecomposedPipelineWithTargetAddWitness n)
    (u : (ZMod (2 ^ n))ˣ) (v z : ZMod (2 ^ n)) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket
          (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
          ((pipelineWithWorkSameCircuit n).encoding.encode
            (initial u v z, cleanWork n)) :
          PureState (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) :
          StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) =
      (PureState.ket
        (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
        ((pipelineWithWorkSameCircuit n).encoding.encode
          (({ denominator := u
              numerator := v
              target := z + quotientResidue u v
              inverseScratch := 0
              quotientScratch := 0
              flag := false } : PipelineState (2 ^ n)),
            cleanWork n)) :
        StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) := by
  simpa [baseWitness, reversiblePipelineStepWithWork_initial] using
    BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness
      (initial u v z, cleanWork n)

/-- Resource counters are projected from the same work-aware decomposed
division circuit. -/
theorem resources_eq {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same work-aware decomposed division
circuit. -/
theorem depth_eq {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same work-aware decomposed division
circuit. -/
theorem queryDepth_eq {n : Nat} (w : DecomposedPipelineWithTargetAddWitness n) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for the clean work-aware division pipeline
statement, conditional on the supplied inverse/product subprograms and the
fixed VBE target-add bridge [PZ03, ecc.tex:622-640; VBE95,
9511018.tex:237-264,591-618]. -/
def cleanResourceCorrectWitness {n : Nat}
    (w : DecomposedPipelineWithTargetAddWitness n) :
    ResourceCorrectWitness
      (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
      (∀ u : (ZMod (2 ^ n))ˣ, ∀ v z : ZMod (2 ^ n),
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket
            (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
            ((pipelineWithWorkSameCircuit n).encoding.encode
              (initial u v z, cleanWork n)) :
            PureState (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) :
            StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)) =
          (PureState.ket
            (R := Qubits (pipelineWithWorkSameCircuit n).encoding.width)
            ((pipelineWithWorkSameCircuit n).encoding.encode
              (({ denominator := u
                  numerator := v
                  target := z + quotientResidue u v
                  inverseScratch := 0
                  quotientScratch := 0
                  flag := false } : PipelineState (2 ^ n)),
                cleanWork n)) :
            StateVector (Qubits (pipelineWithWorkSameCircuit n).encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u v z => apply_clean_ket w u v z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedPipelineWithTargetAddWitness

end PowerOfTwoTargetAddWithAux

/- Finite two-bit integration smoke for the pipeline target-add bridge.  This
reuses the concrete `ZMod 4` Toffoli/CNOT/CNOT target-add-with-aux program
inside the field-packed division pipeline layout; it is not the full
inverse/product/division pipeline [PZ03, ecc.tex:622-640]. -/
namespace Mod4TargetAdd

/-- Tuple-level pipeline target-add witness induced by the concrete `ZMod 4`
modular-addition target update with an auxiliary residue field. -/
def tupleWitness :
    TupleTargetAddWitness
      ModularAddition.TargetAddWithAux.Mod4.residueEncoding :=
  TupleTargetAddWitness.ofModularAddition
    ModularAddition.TargetAddWithAux.Mod4.witness

/-- Same-Circuit pipeline target-add witness over the division `PipelineState 4`
field-packed encoding. -/
def sameCircuit :
    BaseGateSameCircuitWitness (PipelineState 4) addQuotientToTarget :=
  tupleWitness.pipelineWitness

/-- The concrete `ZMod 4` target-add-with-aux program realizes the pipeline
target update after relabeling through the division field tuple. -/
theorem realizes :
    BaseGateProgram.Realizes
      (fieldEncoding ModularAddition.TargetAddWithAux.Mod4.residueEncoding)
      tupleWitness.program addQuotientToTarget :=
  tupleWitness.pipeline_realizes

end Mod4TargetAdd

end PipelineState

/-- Semantic update implemented by a decomposed gate-structured modular
division pipeline witness. -/
abbrev decomposedPipelineStep {N : Nat} : PipelineState N -> PipelineState N :=
  PipelineState.reversiblePipelineStep

/-- Decomposed gate-program witnesses for the reversible inverse/product/add/
uncompute modular-division pipeline [PZ03, ecc.tex:622-640]. -/
structure DecomposedPipelineWitness (N : Nat) where
  /-- Faithful encoding of pipeline labels, including scratch registers. -/
  encoding : BinaryLabelEncoding (PipelineState N)
  /-- Program adding the denominator inverse into inverse scratch. -/
  inverseProgram : BaseGateProgram encoding.width
  /-- Program adding the numerator-inverse product into quotient scratch. -/
  productProgram : BaseGateProgram encoding.width
  /-- Program adding quotient scratch into the target accumulator. -/
  targetAddProgram : BaseGateProgram encoding.width
  /-- Correctness of the inverse-computation program on encoded labels. -/
  inverseRealizes :
    BaseGateProgram.Realizes encoding inverseProgram
      PipelineState.addInverseToScratch
  /-- Correctness of the quotient-product program on encoded labels. -/
  productRealizes :
    BaseGateProgram.Realizes encoding productProgram
      PipelineState.addProductToQuotientScratch
  /-- Correctness of the target-add program on encoded labels. -/
  targetAddRealizes :
    BaseGateProgram.Realizes encoding targetAddProgram
      PipelineState.addQuotientToTarget

namespace DecomposedPipelineWitness

variable {N : Nat}

/-- Build a decomposed pipeline witness over the canonical field-packed
modular-division layout. -/
def ofFieldEncoding {N n : Nat} (E : BinaryResidueEncoding N n)
    (inverseProgram productProgram targetAddProgram :
      BaseGateProgram (PipelineState.fieldEncoding E).width)
    (inverseRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) inverseProgram
        PipelineState.addInverseToScratch)
    (productRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) productProgram
        PipelineState.addProductToQuotientScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) targetAddProgram
        PipelineState.addQuotientToTarget) :
    DecomposedPipelineWitness N where
  encoding := PipelineState.fieldEncoding E
  inverseProgram := inverseProgram
  productProgram := productProgram
  targetAddProgram := targetAddProgram
  inverseRealizes := inverseRealizes
  productRealizes := productRealizes
  targetAddRealizes := targetAddRealizes

@[simp] theorem ofFieldEncoding_encoding {N n : Nat}
    (E : BinaryResidueEncoding N n)
    (inverseProgram productProgram targetAddProgram :
      BaseGateProgram (PipelineState.fieldEncoding E).width)
    (inverseRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) inverseProgram
        PipelineState.addInverseToScratch)
    (productRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) productProgram
        PipelineState.addProductToQuotientScratch)
    (targetAddRealizes :
      BaseGateProgram.Realizes (PipelineState.fieldEncoding E) targetAddProgram
        PipelineState.addQuotientToTarget) :
    (ofFieldEncoding E inverseProgram productProgram targetAddProgram
      inverseRealizes productRealizes targetAddRealizes).encoding =
        PipelineState.fieldEncoding E :=
  rfl

/-- Inverse, product, target-add, reverse-product, and reverse-inverse as one
base-gate program. -/
def program (w : DecomposedPipelineWitness N) :
    BaseGateProgram w.encoding.width :=
  BaseGateProgram.append w.inverseProgram
    (BaseGateProgram.append w.productProgram
      (BaseGateProgram.append w.targetAddProgram
        (BaseGateProgram.append
          (BaseGateProgram.inverse w.productProgram)
          (BaseGateProgram.inverse w.inverseProgram))))

/-- The decomposed program realizes the reversible division pipeline. -/
theorem realizes (w : DecomposedPipelineWitness N) :
    BaseGateProgram.Realizes w.encoding w.program
      (decomposedPipelineStep (N := N)) := by
  have hunproduct :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.inverse w.productProgram)
        PipelineState.subProductFromQuotientScratch :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.productRealizes
      PipelineState.addProductToQuotientScratch_subProductFromQuotientScratch
  have huninverse :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.inverse w.inverseProgram)
        PipelineState.subInverseFromScratch :=
    BaseGateProgram.Realizes.inverse_of_rightInverse w.inverseRealizes
      PipelineState.addInverseToScratch_subInverseFromScratch
  have hcleanup :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.append
          (BaseGateProgram.inverse w.productProgram)
          (BaseGateProgram.inverse w.inverseProgram))
        (fun x : PipelineState N =>
          PipelineState.subInverseFromScratch
            (PipelineState.subProductFromQuotientScratch x)) :=
    BaseGateProgram.Realizes.append
      (firstStep := PipelineState.subProductFromQuotientScratch)
      (secondStep := PipelineState.subInverseFromScratch)
      hunproduct huninverse
  have htargetTail :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.append w.targetAddProgram
          (BaseGateProgram.append
            (BaseGateProgram.inverse w.productProgram)
            (BaseGateProgram.inverse w.inverseProgram)))
        (fun x : PipelineState N =>
          PipelineState.subInverseFromScratch
            (PipelineState.subProductFromQuotientScratch
              (PipelineState.addQuotientToTarget x))) :=
    BaseGateProgram.Realizes.append
      (firstStep := PipelineState.addQuotientToTarget)
      (secondStep := fun x : PipelineState N =>
        PipelineState.subInverseFromScratch
          (PipelineState.subProductFromQuotientScratch x))
      w.targetAddRealizes hcleanup
  have hproductTail :
      BaseGateProgram.Realizes w.encoding
        (BaseGateProgram.append w.productProgram
          (BaseGateProgram.append w.targetAddProgram
            (BaseGateProgram.append
              (BaseGateProgram.inverse w.productProgram)
              (BaseGateProgram.inverse w.inverseProgram))))
        (fun x : PipelineState N =>
          PipelineState.subInverseFromScratch
            (PipelineState.subProductFromQuotientScratch
              (PipelineState.addQuotientToTarget
                (PipelineState.addProductToQuotientScratch x)))) :=
    BaseGateProgram.Realizes.append
      (firstStep := PipelineState.addProductToQuotientScratch)
      (secondStep := fun x : PipelineState N =>
        PipelineState.subInverseFromScratch
          (PipelineState.subProductFromQuotientScratch
            (PipelineState.addQuotientToTarget x)))
      w.productRealizes htargetTail
  have hfull :
      BaseGateProgram.Realizes w.encoding w.program
        (decomposedPipelineStep (N := N)) :=
    BaseGateProgram.Realizes.append
      (firstStep := PipelineState.addInverseToScratch)
      (secondStep := fun x : PipelineState N =>
        PipelineState.subInverseFromScratch
          (PipelineState.subProductFromQuotientScratch
            (PipelineState.addQuotientToTarget
              (PipelineState.addProductToQuotientScratch x))))
      w.inverseRealizes hproductTail
  simpa [program, decomposedPipelineStep, PipelineState.reversiblePipelineStep]
    using hfull

/-- Same-Circuit witness induced by the decomposed division pipeline. -/
def baseWitness (w : DecomposedPipelineWitness N) :
    BaseGateSameCircuitWitness (PipelineState N)
      (decomposedPipelineStep (N := N)) where
  encoding := w.encoding
  program := w.program
  realizes := w.realizes

/-- The decomposed division circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : DecomposedPipelineWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w.baseWitness

/-- Encoded-basis correctness for all staged modular-division labels. -/
theorem apply_ket (w : DecomposedPipelineWitness N) (x : PipelineState N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode (PipelineState.reversiblePipelineStep x)) :
        StateVector (Qubits w.encoding.width)) :=
  BaseGateSameCircuitWitness.apply_encoded_ket w.baseWitness x

/-- Clean staged action:
`|enc(u,v,z,0,0,0)> -> |enc(u,v,z+v*u^{-1},0,0,0)>`. -/
theorem apply_clean_ket (w : DecomposedPipelineWitness N)
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode (PipelineState.initial u v z)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ denominator := u
             numerator := v
             target := z + quotientResidue u v
             inverseScratch := 0
             quotientScratch := 0
             flag := false } : PipelineState N)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [PipelineState.reversiblePipelineStep_initial] using
    apply_ket w (PipelineState.initial u v z)

/-- Resource counters are projected from the same decomposed division circuit. -/
theorem resources_eq (w : DecomposedPipelineWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
      (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w.baseWitness

/-- Circuit depth is projected from the same decomposed division circuit. -/
theorem depth_eq (w : DecomposedPipelineWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w.baseWitness

/-- Query depth is projected from the same decomposed division circuit. -/
theorem queryDepth_eq (w : DecomposedPipelineWitness N) :
    (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
      (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w.baseWitness

/-- Resource-correct witness for the clean staged encoded modular-division
statement, conditional on concrete decomposed subprograms supplied by `w`. -/
def cleanResourceCorrectWitness (w : DecomposedPipelineWitness N) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : (ZMod N)ˣ, ∀ v z : ZMod N,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w.baseWitness)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode (PipelineState.initial u v z)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ denominator := u
                 numerator := v
                 target := z + quotientResidue u v
                 inverseScratch := 0
                 quotientScratch := 0
                 flag := false } : PipelineState N)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w.baseWitness).resources =
          (BaseGateSameCircuitWitness.profile w.baseWitness).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).depth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w.baseWitness).queryDepth =
          (BaseGateSameCircuitWitness.profile w.baseWitness).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w.baseWitness
  correctness := fun u v z => apply_clean_ket w u v z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end DecomposedPipelineWitness

/-- Semantic update implemented by a gate-structured modular-division witness. -/
abbrev encodedStep {N : Nat} : Data N -> Data N :=
  Data.addQuotientIntoTarget

/-- Gate-structured encoded modular-division witness. -/
abbrev StructuredCircuitWitness (N : Nat) :=
  BaseGateSameCircuitWitness (Data N) (encodedStep (N := N))

namespace StructuredCircuitWitness

variable {N : Nat}

/-- The structured division circuit history bottoms out in X/CNOT/Toffoli atoms. -/
theorem structured (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).history.IsBaseGateStructured :=
  BaseGateSameCircuitWitness.structured w

/-- Encoded-basis correctness for all modular-division data labels. -/
theorem apply_ket (w : StructuredCircuitWitness N) (x : Data N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width) (w.encoding.encode x) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode x.addQuotientIntoTarget) :
        StateVector (Qubits w.encoding.width)) :=
  by
    simpa [encodedStep] using BaseGateSameCircuitWitness.apply_encoded_ket w x

/-- Clean public-form encoded-basis action:
`|enc(u,v,z,0)> -> |enc(u,v,z+v*u^{-1},0)>`. -/
theorem apply_clean_ket (w : StructuredCircuitWitness N)
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Circuit.apply (BaseGateSameCircuitWitness.circuit w)
        ((PureState.ket (R := Qubits w.encoding.width)
          (w.encoding.encode
            ({ denominator := u, numerator := v, target := z, flag := false } :
              Data N)) :
          PureState (Qubits w.encoding.width)) :
          StateVector (Qubits w.encoding.width)) =
      (PureState.ket (R := Qubits w.encoding.width)
        (w.encoding.encode
          ({ denominator := u
             numerator := v
             target := z + quotientResidue u v
             flag := false } : Data N)) :
        StateVector (Qubits w.encoding.width)) := by
  simpa [encodedStep, Data.addQuotientIntoTarget] using
    apply_ket (N := N) w
      ({ denominator := u, numerator := v, target := z, flag := false } : Data N)

/-- Resource counters are projected from the same structured division circuit. -/
theorem resources_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).resources =
      (BaseGateSameCircuitWitness.profile w).toResourceProfile :=
  BaseGateSameCircuitWitness.resources_eq w

/-- Circuit depth is projected from the same structured division circuit. -/
theorem depth_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).depth =
      (BaseGateSameCircuitWitness.profile w).circuitDepth :=
  BaseGateSameCircuitWitness.depth_eq w

/-- Query depth is projected from the same structured division circuit. -/
theorem queryDepth_eq (w : StructuredCircuitWitness N) :
    (BaseGateSameCircuitWitness.circuit w).queryDepth =
      (BaseGateSameCircuitWitness.profile w).oracleQueries :=
  BaseGateSameCircuitWitness.queryDepth_eq w

/-- Resource-correct witness for the clean encoded modular-division statement. -/
def cleanResourceCorrectWitness (w : StructuredCircuitWitness N) :
    ResourceCorrectWitness (R := Qubits w.encoding.width)
      (∀ u : (ZMod N)ˣ, ∀ v z : ZMod N,
        Circuit.apply (BaseGateSameCircuitWitness.circuit w)
          ((PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ denominator := u, numerator := v, target := z, flag := false } :
                Data N)) :
            PureState (Qubits w.encoding.width)) :
            StateVector (Qubits w.encoding.width)) =
          (PureState.ket (R := Qubits w.encoding.width)
            (w.encoding.encode
              ({ denominator := u
                 numerator := v
                 target := z + quotientResidue u v
                 flag := false } : Data N)) :
            StateVector (Qubits w.encoding.width)))
      ((BaseGateSameCircuitWitness.circuit w).resources =
          (BaseGateSameCircuitWitness.profile w).toResourceProfile ∧
        (BaseGateSameCircuitWitness.circuit w).depth =
          (BaseGateSameCircuitWitness.profile w).circuitDepth ∧
        (BaseGateSameCircuitWitness.circuit w).queryDepth =
          (BaseGateSameCircuitWitness.profile w).oracleQueries) where
  circuit := BaseGateSameCircuitWitness.circuit w
  correctness := fun u v z => apply_clean_ket w u v z
  resources := ⟨resources_eq w, depth_eq w, queryDepth_eq w⟩

end StructuredCircuitWitness

end

end ModularDivision
end QuantumAlg
