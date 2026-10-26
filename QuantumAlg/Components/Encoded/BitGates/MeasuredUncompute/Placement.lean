/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Branch
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Semantics
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

import all QuantumAlg.Core.Execution.Classical.MapLaws

/-!
# Actual measured reset through complete physical-wire equality

The native H and the outcome-selected identity/X are placed on the same
ordered physical systems. The MZ instruction reads the corresponding actual
wire. The equality below uses complete wire records, including physical
identities and dimensions, rather than an equality of register sizes
[G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

open Execution
open scoped BigOperators Kronecker

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}
  (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
  (ctx : RuntimeCtx .quantum)
  (sameWires : layout.toQuantum.wires = ctx.quantumLayout.wires)

/-- The measured target is the corresponding position in the full actual wire list. -/
def placedWire : Fin ctx.systemCount :=
  positionsOfEqualWires layout.toQuantum ctx.quantumLayout sameWires target.wire

/-- Correspondence preserves the selected wire's physical dimension. -/
lemma placedWire_qubit : (ctx.quantumLayout.wire
    (placedWire target layout ctx sameWires)).dimension = 2 :=
  congrArg QuantumWire.dimension
    (wireAtCorrespondingPosition layout.toQuantum ctx.quantumLayout sameWires target.wire)

/-- Convert only the finite label of that same physical qubit. -/
def placedOutcome
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension) :
    Fin 2 :=
  Fin.cast (congrArg PNat.val (placedWire_qubit target layout ctx sameWires)) outcome

/-- Native H placed by equality of the complete ordered wire records. -/
def placedHadamard : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout :=
  unitaryOfEqualWires layout.toQuantum ctx.quantumLayout sameWires
    (target.hadamard layout oracles)

/-- The actual selected identity/X is placed by precisely the same wire certificate. -/
def placedCorrection
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension) :
    UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout :=
  unitaryOfEqualWires layout.toQuantum ctx.quantumLayout sameWires
    (correction target layout (placedOutcome target layout ctx sameWires outcome))

/-- Execute the placed native word, actual MZ/write and read-back selected native reset. -/
def placedCircuit
    (output : CWriteRef ctx
      (.finite (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx allowAllocation :=
  (Circuit.unitary (placedHadamard (oracles := oracles) target layout ctx sameWires)).seq
    ((Circuit.measureZ (placedWire target layout ctx sameWires) output).seq
      (.branch (.storage output.toCStorageRef) (fun value =>
        .unitary (placedCorrection target layout ctx sameWires value.toFin))))

/-- The corresponding actual basis coordinate keeps its exact original finite value. -/
lemma placedBasis_read (state : layout.toQuantum.Basis) :
    actualOutcome target layout (placedOutcome target layout ctx sameWires
      ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires state)
        (placedWire target layout ctx sameWires))) = state target.wire := by
  apply Fin.ext
  exact basisOfEqualWires_value layout.toQuantum ctx.quantumLayout sameWires state target.wire

/-- One physical branch of the actual placed instruction word, including the reference identity. -/
def placedKraus (environment : oracles.Interpretation)
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension)
    (Reference : Register) : HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor
    ((placedCorrection target layout ctx sameWires outcome).matrix environment)
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
    ZMeasurement.projector
      (fun basis : (Register.prod ctx.register Reference).Index =>
        basis.1 (placedWire target layout ctx sameWires)) outcome *
    (UnitaryOperator.prodTensor
      ((placedHadamard target layout ctx sameWires).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference))

/-- The exact chronological record keeps old history and overwrites only the supplied cell. -/
def placedRecord
    (output : CWriteRef ctx
      (.finite (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty)
    {allowAllocation : Bool} {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension) :
    Store ctx × (services.HiddenState ×
      (History × (placedCircuit (oracles := oracles) target layout ctx sameWires output
        operations services allowAllocation).Path)) :=
  (entry.1.write output (.finite outcome),
    (entry.2.1, (entry.2.2, ((), (outcome, ⟨.finite outcome, ()⟩)))))

/-- Full actual execution retains all original stores and every physical measurement outcome. -/
lemma placedCircuit_execute {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {allowAllocation : Bool}
    (output : CWriteRef ctx
      (.finite (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (placedCircuit target layout ctx sameWires output operations services allowAllocation).execute
        environment Reference state =
      ((ExecutionState.measureZ
        (state.applyUnitary fun _ => UnitaryOperator.prodTensor
          ((placedHadamard target layout ctx sameWires).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (fun basis : (Register.prod ctx.register Reference).Index =>
          basis.1 (placedWire target layout ctx sameWires))).applyUnitary
          fun entry => UnitaryOperator.prodTensor
            ((placedCorrection target layout ctx sameWires entry.2).matrix environment.quantum)
            (1 : UnitaryOperator Reference)).mapClassical
              (fun entry => placedRecord (oracles := oracles) target layout ctx sameWires output
                operations services entry.1 entry.2) := by
  unfold placedCircuit
  rw [Circuit.execute_seq, Circuit.execute_unitary,
    Circuit.execute_seq, Circuit.execute_measureZ, Circuit.selectedUnitary_execute]
  simp only [State.mapHistory, ExecutionState.mapClassical_measureZ,
    ExecutionState.applyUnitary_mapClassical, Store.read_write_same, CShape.Value.toFin_finite,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × (services.HiddenState × History)) ×
          Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension =>
        (show Store ctx × (services.HiddenState ×
        (History × (placedCircuit (oracles := oracles) target layout ctx sameWires output
          operations services allowAllocation).Path)) from
          (entry.1.1.write output (.finite entry.2),
          (entry.1.2.1, (entry.1.2.2, ((), (entry.2,
            ⟨(entry.1.1.write output (.finite entry.2)).read
              (.storage output.toCStorageRef), ()⟩))))))) =
      (fun entry => placedRecord (oracles := oracles) target layout ctx sameWires output
        operations services entry.1 entry.2) := by
    funext entry
    exact congrArg
      (fun value : (CShape.finite (ctx.quantumLayout.wire (placedWire target layout ctx
        sameWires)).dimension).Value =>
        (show Store ctx × (services.HiddenState ×
        (History × (placedCircuit (oracles := oracles) target layout ctx sameWires output
          operations services allowAllocation).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, ((), (entry.2, ⟨value, ()⟩)))))))
      (Store.read_write_same entry.1.1 output (.finite entry.2))
  have updated := congrArg (fun update =>
    ((ExecutionState.measureZ
      (state.applyUnitary fun _ => UnitaryOperator.prodTensor
        ((placedHadamard target layout ctx sameWires).matrix environment.quantum) (1 :
          UnitaryOperator Reference))
      (fun basis : (Register.prod ctx.register Reference).Index => basis.1 (placedWire target
        layout ctx sameWires))).applyUnitary
        fun entry => UnitaryOperator.prodTensor
          ((placedCorrection target layout ctx sameWires entry.2).matrix environment.quantum) (1
            : UnitaryOperator Reference)).mapClassical update) readBack
  refine Eq.trans ?_ updated
  congr 1
  exact Subsingleton.elim _ _

/-- Every output block is the exact sum of the actual record-conditioned Kraus branches. -/
lemma placedCircuit_block_matrix {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {allowAllocation : Bool}
    (output : CWriteRef ctx
      (.finite (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (placedCircuit (oracles := oracles) target layout ctx sameWires output
        operations services allowAllocation).Path)))
    (left right : (Register.prod ctx.register Reference).Index) :
    (((placedCircuit target layout ctx sameWires output operations services allowAllocation).execute
      environment Reference state).block result).matrix left right =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome,
        if placedRecord (oracles := oracles) target layout ctx sameWires output
            operations services original outcome = result then
          (placedKraus target layout ctx sameWires environment.quantum outcome Reference *
            (state.block original).matrix *
              (placedKraus target layout ctx sameWires environment.quantum outcome
                Reference).conjTranspose) left right
        else 0 := by
  rw [placedCircuit_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs
  · rw [ExecutionState.measureZ_block]
    simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
      ZMeasurement.branch, placedKraus,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rfl

private lemma projector_reference {Local Reference : Register} {Outcome : Type}
    [DecidableEq Outcome]
    (readout : Local.Index → Outcome) (outcome : Outcome) :
    ZMeasurement.projector (fun basis : (Register.prod Local Reference).Index =>
      readout basis.1) outcome =
        ZMeasurement.projector readout outcome ⊗ₖ (1 : HilbertOperator Reference) := by
  ext row column
  rcases row with ⟨rowLocal, rowReference⟩
  rcases column with ⟨columnLocal, columnReference⟩
  change (if (rowLocal, rowReference) = (columnLocal, columnReference) then
      (if readout rowLocal = outcome then (1 : ℂ) else 0) else 0) =
    (if rowLocal = columnLocal then (if readout rowLocal = outcome then 1 else 0) else 0) *
      (if rowReference = columnReference then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma placed_projector (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension) :
    ZMeasurement.projector
        (fun basis : (Register.prod ctx.register Reference).Index =>
          basis.1 (placedWire target layout ctx sameWires)) outcome =
      (ZMeasurement.projector
        (fun basis : (Register.prod layout.toQuantum.register Reference).Index =>
          basis.1 target.wire)
          (actualOutcome target layout (placedOutcome target layout ctx sameWires
            outcome))).submatrix
            ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
              (Equiv.refl Reference.Index)).symm
            ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
              (Equiv.refl Reference.Index)).symm := by
  unfold ZMeasurement.projector
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext basis
  have read := placedBasis_read target layout ctx sameWires
    ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).symm basis.1)
  rw [Equiv.apply_symm_apply] at read
  have selected : basis.1 (placedWire target layout ctx sameWires) = outcome ↔
      ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).symm basis.1)
          target.wire = actualOutcome target layout
            (placedOutcome target layout ctx sameWires outcome) := by
    constructor
    · intro equal
      exact read.symm.trans (congrArg (fun value => actualOutcome target layout
        (placedOutcome target layout ctx sameWires value)) equal)
    · intro equal
      apply Fin.ext
      have sameValue := congrArg
        (fun value : Fin (layout.toQuantum.wire target.wire).dimension => value.val)
        (read.trans equal)
      exact sameValue
  change (if basis.1 (placedWire target layout ctx sameWires) = outcome then (1 : ℂ) else 0) =
    (if ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).symm basis.1)
        target.wire = actualOutcome target layout (placedOutcome target layout ctx sameWires
          outcome) then 1 else 0)
  exact if_congr selected rfl rfl

private lemma tensor_reindex {Source Target Reference : Register}
    (coordinates : Source.Index ≃ Target.Index) (operator : UnitaryOperator Source) :
    (UnitaryOperator.prodTensor (UnitaryOperator.reindex coordinates operator)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod Target Reference)) =
      ((operator : HilbertOperator Source) ⊗ₖ (1 : HilbertOperator Reference)).submatrix
        (coordinates.prodCongr (Equiv.refl Reference.Index)).symm
        (coordinates.prodCongr (Equiv.refl Reference.Index)).symm := by
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

/-- The actual placed branch is exactly the encoded native branch on those same physical wires. -/
lemma placedKraus_eq (environment : oracles.Interpretation)
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension)
    (Reference : Register) :
    placedKraus target layout ctx sameWires environment outcome Reference =
      (branchOperator (environment := environment) target layout
        (placedOutcome target layout ctx sameWires outcome) Reference).submatrix
          ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm
          ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index)).symm := by
  rw [placedKraus, placedHadamard, placedCorrection, unitaryOfEqualWires_matrix,
    unitaryOfEqualWires_matrix, tensor_reindex, tensor_reindex,
    placed_projector,
    projector_reference (Local := layout.toQuantum.register) (Reference := Reference)
      (fun basis : layout.toQuantum.register.Index => basis target.wire)
      (actualOutcome target layout (placedOutcome target layout ctx sameWires outcome)),
    Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  congr 1
  rw [branchOperator, nativeBranch, projector]
  let first : HilbertOperator layout.toQuantum.register :=
    (correction target layout (placedOutcome target layout ctx sameWires outcome)).matrix
      environment
  let middle : HilbertOperator layout.toQuantum.register :=
    projector target layout (placedOutcome target layout ctx sameWires outcome)
  let last : HilbertOperator layout.toQuantum.register :=
    (target.hadamard layout oracles).matrix environment
  let reference : HilbertOperator Reference := 1
  have firstProduct : (first ⊗ₖ reference) * (middle ⊗ₖ reference) =
      (first * middle) ⊗ₖ reference := by
    simpa only [reference, Matrix.one_mul] using
      (Matrix.mul_kronecker_mul first middle reference reference).symm
  have complete : ((first * middle) ⊗ₖ reference) * (last ⊗ₖ reference) =
      (first * middle * last) ⊗ₖ reference := by
    simpa only [reference, Matrix.one_mul] using
      (Matrix.mul_kronecker_mul (first * middle) last reference reference).symm
  exact (congrArg (fun value => value * (last ⊗ₖ reference)) firstProduct).trans complete

private lemma matrix_reindex_applyVec {Source Target : Register}
    (coordinates : Source.Index ≃ Target.Index) (operator : HilbertOperator Source)
    (vector : HilbertVector Source) :
    HilbertOperator.applyVec (R := Target) (operator.submatrix coordinates.symm coordinates.symm)
        (HilbertVector.reindex coordinates vector) =
      HilbertVector.reindex coordinates (operator.applyVec vector) := by
  apply WithLp.ofLp_injective
  funext output
  simp only [HilbertOperator.applyVec_apply,
    HilbertVector.reindex_apply]
  change (∑ input : Target.Index, operator (coordinates.symm output)
      (coordinates.symm input) * vector (coordinates.symm input)) =
    ∑ input : Source.Index, operator (coordinates.symm output) input * vector input
  exact Equiv.sum_comp coordinates.symm
    (fun input => operator (coordinates.symm output) input * vector input)

/-- Actual ctx-level per-record coherent action, preserving every dirty and reference amplitude. -/
lemma placedKraus_coherent_reference (environment : oracles.Interpretation)
    (outcome : Fin (ctx.quantumLayout.wire (placedWire target layout ctx sameWires)).dimension)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (placedKraus target layout ctx sameWires environment outcome Reference).applyVec
        (HilbertVector.reindex
          ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index))
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
              (layout.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)) =
      HilbertVector.reindex
        ((basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index))
        (∑ index, (amplitude index * (NormalizedVector.invSqrt2 *
            character (placedOutcome target layout ctx sameWires outcome)
              (target.get (state index)))) •
          (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
            (layout.basisEquiv.symm (encoding.encode (resetLabel target (state index))),
              reference index)).vec) := by
  rw [placedKraus_eq, matrix_reindex_applyVec, branch_coherent_reference]

/-- The same target physical wire is zero in every retained branch ket. -/
lemma placed_reset_zero (state : Data) :
    (basisOfEqualWires layout.toQuantum ctx.quantumLayout sameWires
      (layout.basisEquiv.symm (encoding.encode (resetLabel target state))))
        (placedWire target layout ctx sameWires) = 0 := by
  apply Fin.ext
  have actual := basisOfEqualWires_value layout.toQuantum ctx.quantumLayout sameWires
    (layout.basisEquiv.symm (encoding.encode (resetLabel target state))) target.wire
  refine actual.trans ?_
  rw [physical_get]
  unfold resetLabel
  cases value : target.get state <;> simp [value, get_flip_self, finTwoEquiv, actualOutcome]

end

end QuantumAlg.EncodedBit.MeasuredUncompute
