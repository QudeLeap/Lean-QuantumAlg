/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Exact actual-Store transport of the chronological retained native operators

A static assignment represents an actual record only when each physical
measurement and each later paid phase read agrees with it. The recursive
condition below follows the actual intermediate Stores. Equal-wire operator
transport retains complete ordered physical wire identities and every
external reference; it is not a dimension-only identification
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The physical outcome or actual stored phase read agrees with the same retained assignment. -/
def ConsistentOutcome (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) (outcome : Fin records → Fin 2)
    (instruction : Instruction encoding records) (store : Store ctx) :
    instruction.PhysicalOutcome physical sameWires → Prop :=
  match instruction with
  | .native _ => fun _ => True
  | .vent target record => fun measured =>
      EncodedBit.MeasuredUncompute.placedOutcome target physical ctx sameWires measured =
        outcome record
  | .phase _ record => fun _ =>
      (store.read (.storage (output record).toCStorageRef)).toFin = outcome record

/-- Every factor uses the actual Store left by its preceding physical instructions. -/
def WordConsistent (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) (outcome : Fin records → Fin 2) :
    (word : List (Instruction encoding records)) → Store ctx →
      WordOutcomes physical sameWires word → Prop
  | [], _, _ => True
  | instruction :: rest, store, measured =>
      ConsistentOutcome physical sameWires output outcome instruction store measured.1 ∧
        WordConsistent physical sameWires output outcome rest
          (instruction.actualRecord (oracles := oracles) (operations := operations)
            (services := services) physical sameWires output store measured.1).1 measured.2

private lemma placed_tensor (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (environment : oracles.Interpretation) (Reference : Register)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    (UnitaryOperator.prodTensor
      ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program).matrix
        environment) (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod ctx.register Reference)) =
      (UnitaryOperator.prodTensor (program.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod physical.toQuantum.register Reference)).submatrix
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm := by
  rw [unitaryOfEqualWires_matrix]
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

/-- The actual retained factor is the same native encoded factor at the actual Store read. -/
lemma actualKraus_eq_branch (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (Reference : Register)
    (outcome : Fin records → Fin 2) (instruction : Instruction encoding records)
    (store : Store ctx) (measured : instruction.PhysicalOutcome physical sameWires)
    (consistent : ConsistentOutcome physical sameWires output outcome instruction store measured) :
    instruction.actualKraus physical sameWires output environment Reference store measured =
      (instruction.branchOperator physical environment Reference outcome).submatrix
        ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index)).symm
        ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index)).symm := by
  cases instruction with
  | native gates => exact placed_tensor physical sameWires environment Reference _
  | vent target record =>
      change EncodedBit.MeasuredUncompute.placedOutcome target physical ctx sameWires measured =
        outcome record at consistent
      have actual := EncodedBit.MeasuredUncompute.placedKraus_eq target physical ctx sameWires
        environment measured Reference
      rw [consistent] at actual
      exact actual
  | phase target record =>
      change (store.read (.storage (output record).toCStorageRef)).toFin = outcome record
        at consistent
      rw [actualKraus, consistent]
      exact placed_tensor physical sameWires environment Reference _

/-- The actual full chronological operator equals the consistently retained encoded native word. -/
lemma wordActualKraus_eq_branch (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (Reference : Register)
    (outcome : Fin records → Fin 2) :
    ∀ (word : List (Instruction encoding records)) (store : Store ctx)
      (measured : WordOutcomes physical sameWires word),
    WordConsistent (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output outcome word store measured →
      wordActualKraus (operations := operations) (services := services) physical sameWires output
          environment Reference word store measured =
        (wordBranch physical environment Reference outcome word).submatrix
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm := by
  intro word
  induction word with
  | nil =>
      intro store measured _
      rw [wordActualKraus, wordBranch, Matrix.submatrix_one_equiv]
  | cons instruction rest ih =>
      intro store measured consistent
      rw [wordActualKraus, ih _ _ consistent.2,
        actualKraus_eq_branch physical sameWires output environment Reference outcome instruction
          store measured.1 consistent.1, wordBranch, Matrix.submatrix_mul_equiv]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
