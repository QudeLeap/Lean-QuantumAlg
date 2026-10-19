/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Initialization.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Reference
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Initialized.Paths
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Observation
import all QuantumAlg.Core.Base.State.Density.ReferenceBlock
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# One actual leading reset on the existing reduced ECC terminal

This is the reduced-layout replacement for the existing leading sampling-reset role, not
an additional reset in a completed algorithm. Every resident qubit is actually measured
into the existing numerator cell zero and corrected by its actual stored outcome. The
complete Store, service state, incoming history and actual reset Path remain in each
conditional Reference block, without branch normalization.

Only the bare ECCCaller.terminal is constructed here. No public frame,
initializer, terminal sigma, success/retry or upper-level resource theorem is
provided. The arbitrary incoming State need not satisfy any initialized,
canonical-classical-cell or good-trajectory condition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement MAU.Inversion.SharedEEA MeasuredPointAddition
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def QubitContext (ctx : RuntimeCtx .quantum) : Prop :=
  ∀ wire ∈ ctx.quantumWires, wire.dimension = 2

private lemma qubitLayout_member {width : Nat} (layout : QubitLayout width)
    (wire : QuantumWire) (present : wire ∈ layout.toQuantumLayout.wires) :
    wire.dimension = 2 := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rfl

private lemma owned_qubits (ctx : RuntimeCtx .quantum) (key : StorageKey)
    {count : Nat} (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (original : QubitContext ctx)
    (added : ∀ wire ∈ layout.wires, wire.dimension = 2) :
    QubitContext (ctx.addOwnedLayout key layout fresh disjoint) := by
  intro wire present
  rw [RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout] at present
  exact (List.mem_append.mp present).elim (added wire) (original wire)

private lemma cells_qubits (ctx : RuntimeCtx .quantum) (dimension : ℕ+) (count : Nat)
    (original : QubitContext ctx) :
    QubitContext (MeasurementCells.context ctx dimension count) := by
  intro wire present
  rw [MeasurementCells.context_quantumWires] at present
  exact original wire present

private lemma union_qubits (left right : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : QubitContext left) (second : QubitContext right) :
    QubitContext (left.disjointUnion right separate) := by
  intro wire present
  rw [RuntimeCtx.quantumWires_disjointUnion] at present
  exact (List.mem_append.mp present).elim (first wire) (second wire)

private lemma indexed_qubits (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    QubitContext (indexedContext width indices distinct) := by
  intro wire present
  change wire ∈ (indices.map (indexedEntry width)).flatMap RuntimeEntry.quantumWires at present
  rw [indexed_wires] at present
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  rfl

private lemma numerator_qubits (width : Nat) :
    QubitContext (NumeratorMeasurement.context width) := by
  have supplied : QubitContext (InversePreparation.before width) :=
    owned_qubits RuntimeCtx.empty ⟨0⟩ (InversePreparation.inputLayout width) (by decide)
      (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])
      (by intro wire present; exact False.elim (List.not_mem_nil present))
      (qubitLayout_member (InversePreparation.inputQubitLayout width))
  have arithmetic : QubitContext (InversePreparation.after width) :=
    owned_qubits (InversePreparation.before width) InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
      (InversePreparation.auxiliary_disjoint width) supplied
      (qubitLayout_member (InputPreparation.auxiliaryQubitLayout width))
  exact cells_qubits (InversePreparation.after width) 2 width arithmetic

private lemma ready_qubits (width : Nat) : QubitContext (Recovery.Layout.bank width) :=
  union_qubits _ _ (indexedContext_disjoint width (List.range 3) List.nodup_range)
    (numerator_qubits width) (indexed_qubits width (List.range 3) List.nodup_range)

/-- Every resident reduced-terminal system is an actual qubit, including C/M/N and auxiliaries. -/
lemma newReset_qubits (width m : Nat) (wire : Fin (Recovery.Layout.terminal width
  m).systemCount) :
    ((Recovery.Layout.terminal width m).quantumLayout.wire wire).dimension = 2 := by
  have all := cells_qubits (Recovery.Layout.bank width) 2 (2 * m) (ready_qubits width)
  apply all
  rw [← RuntimeCtx.quantumLayout_wires, QuantumLayout.wires]
  exact List.mem_ofFn.mpr ⟨wire, rfl⟩

private lemma liftWrite_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (dimension : ℕ+) (ref : CWriteRef ctx shape) (count : Nat) :
    (MeasurementCells.liftWrite dimension ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

private lemma finiteCastWrite_key {ctx : RuntimeCtx .quantum} {first second : ℕ+}
    (same : first = second) (ref : CWriteRef ctx (.finite first)) :
    (same ▸ ref : CWriteRef ctx (.finite second)).key = ref.key := by
  cases same
  rfl

/-- The real numerator cell zero exists for every prime field, including exponent width zero. -/
def scratchIndex (p : Nat) [Fact p.Prime] : Fin p.size :=
  ⟨0, Nat.size_pos.mpr (Nat.Prime.pos (Fact.out : p.Prime))⟩

/-- Lift the existing numerator scratch through the actual ready union and terminal cells. -/
def newResetScratch (p m : Nat) [Fact p.Prime] :
    CWriteRef (Recovery.Layout.terminal p.size m) (.finite 2) :=
  MeasurementCells.liftWrite 2
    (ContextUnion.writeLeft
      (indexedContext_disjoint p.size (List.range 3) List.nodup_range)
      (NumeratorMeasurement.cell p.size (scratchIndex p))) (2 * m)

/-- The scratch retains its original physical storage identity; no terminal result cell is used. -/
lemma newResetScratch_key (p m : Nat) [Fact p.Prime] :
    (newResetScratch p m).key = (NumeratorMeasurement.cell p.size (scratchIndex p)).key := by
  rw [newResetScratch, liftWrite_key]
  rfl

/-- Each measured physical dimension uses the same existing scratch after its exact dimension cast.
-/
def newResetCells (p m : Nat) [Fact p.Prime]
    (wire : Fin (Recovery.Layout.terminal p.size m).systemCount) :
    CWriteRef (Recovery.Layout.terminal p.size m)
      (.finite ((Recovery.Layout.terminal p.size m).quantumLayout.wire wire).dimension) :=
  (newReset_qubits p.size m wire).symm ▸ newResetScratch p m

/-- Dimension casts cannot change the actual written storage key. -/
lemma newResetCells_key (p m : Nat) [Fact p.Prime]
    (wire : Fin (Recovery.Layout.terminal p.size m).systemCount) :
    (newResetCells p m wire).key = (newResetScratch p m).key :=
  finiteCastWrite_key (newReset_qubits p.size m wire).symm (newResetScratch p m)

/-- The exact native correction on every actual wire is identity or one placed Pauli X. -/
def newResetImplementations (width m : Nat)
    (wire : Fin (Recovery.Layout.terminal width m).systemCount) :
    QuditShift.Realizations AlgorithmGate.model .empty
      (Recovery.Layout.terminal width m).quantumLayout wire :=
  QuditShift.qubitRealizations (Recovery.Layout.terminal width m).quantumLayout wire
    (newReset_qubits width m wire) .empty

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

/-- The actual arithmetic target retains the original auxiliaries and Montgomery seed coordinates.
-/
def resetArithmeticLabel : (NumeratorMeasurement.context p.size).register.Index :=
  Recovery.Reference.Exponents.arithmeticBasis p.size
    ((InPlacePreparation.preparation p).value,
      (fieldWord ((2 : ZMod p) ^ fieldTail.succ * seed.x),
        fieldWord ((2 : ZMod p) ^ fieldTail.succ * seed.y)))

/-- Assemble the actual point C/N zero target beside the existing memory qubit M = zero. -/
def resetReadyLabel : (Recovery.Layout.bank p.size).register.Index :=
  (Recovery.Point.indexedPointPlacement p.size (0 : Fin 2)).basis.symm
    (MeasuredPointAddition.label p.size 0 0 (resetArithmeticLabel E fieldTail seed),
      (memoryBasis p.size).symm 0)

/-- The result frame is quantum-empty, while all its classical cells remain physically resident. -/
def newResetLabel : (Recovery.Layout.terminal p.size m).register.Index :=
  (Recovery.Point.cellsPlacement (Recovery.Layout.bank p.size) 2 (2 * m)).basis.symm
    (resetReadyLabel E fieldTail seed, (Recovery.Layout.Reference.frameBasis p.size m).symm ())

/-- The concrete physical target is exactly the existing J00 column of the original common seed. -/
lemma newResetLabel_initializedBasis (Reference : Register) (reference : Reference.Index) :
    initializedBasis p.size m Reference
      ((Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference reference)) =
      (newResetLabel E fieldTail m seed, reference) := by
  change (Recovery.Stage.PointCoordinates.coordinates p.size m Reference).symm
    (0, (0, (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
      (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference reference))) = _
  rw [Recovery.Stage.PointCoordinates.coordinates_symm]
  simp only [Recovery.Layout.Reference.bankBasis_symm]
  rfl

/-- C/M are zero and the full bank is the actual old reset seed at every external Reference value.
-/
lemma newResetLabel_coordinates (Reference : Register) (reference : Reference.Index) :
    Recovery.Stage.PointCoordinates.coordinates p.size m Reference
      (newResetLabel E fieldTail m seed, reference) =
        (0, (0, (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
          (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference
            reference))) := by
  rw [← newResetLabel_initializedBasis E fieldTail m seed Reference reference]
  change (Recovery.Stage.PointCoordinates.coordinates p.size m Reference)
    ((Recovery.Stage.PointCoordinates.coordinates p.size m Reference).symm _) = _
  exact Equiv.apply_symm_apply _ _

/-- The one actual allocation-free replacement reset measures and corrects every resident wire once.
-/
def newReset : Circuit (.quantum AlgorithmGate.model .empty)
    (Recovery.Layout.terminal p.size m) (Recovery.Layout.terminal p.size m) false :=
  QuditShift.resetToBasis (allowAllocation := false)
    (newResetImplementations p.size m) (newResetCells p m) (newResetLabel E fieldTail m seed)

/-- Complete final record: no Store cell, service value, incoming history or actual reset Path is
dropped. -/
abbrev ResetRecord (History : Type) :=
  Store (Recovery.Layout.terminal p.size m) ×
    (ClassicalOracleModel.empty.HiddenState ×
      (History × (newReset E fieldTail m seed).Path))

variable {Reference : Register} {History : Type} [Fintype History]

/-- Each actual complete record has its prescribed local ket and full off-diagonal Reference
coefficient. -/
lemma newReset_block_factor
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History)
    (left right : (Recovery.Layout.terminal p.size m).register.Index)
    (refLeft refRight : Reference.Index) :
    (((newReset E fieldTail m seed).execute environment Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) left *
        (((newReset E fieldTail m seed).execute environment Reference state).block record).matrix
          (newResetLabel E fieldTail m seed, refLeft)
          (newResetLabel E fieldTail m seed, refRight) *
        star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) right) :=
  QuditShift.resetToBasis_block_factor (allowAllocation := false)
    (implementations := newResetImplementations p.size m)
    (newResetCells p m) (newResetLabel E fieldTail m seed) state record left right refLeft refRight

/-- The actual positive subnormalized Reference block, without conditional normalization. -/
def newResetReferenceCoefficient
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History) : DensityOperator Reference :=
  (((newReset E fieldTail m seed).execute environment Reference state).block record).basisSlice
    (newResetLabel E fieldTail m seed)

/-- Every complex Reference entry is the same entry in that actual full Store/history/path block. -/
lemma newResetReferenceCoefficient_matrix
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History) (left right : Reference.Index) :
    (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
      record).matrix left right =
      (((newReset E fieldTail m seed).execute environment Reference state).block record).matrix
        (newResetLabel E fieldTail m seed, left) (newResetLabel E fieldTail m seed, right) := rfl

/-- Each actual density block factors through the positive Reference coefficient on the same record.
-/
lemma newReset_record_factor
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History)
    (left right : (Recovery.Layout.terminal p.size m).register.Index)
    (refLeft refRight : Reference.Index) :
    (((newReset E fieldTail m seed).execute environment Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) left *
        (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
          record).matrix refLeft refRight *
        star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) right) :=
  newReset_block_factor E fieldTail m seed state record left right refLeft refRight

/-- The slice keeps exactly this complete record's original mass, even when that mass is zero. -/
lemma newResetReferenceCoefficient_mass
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History) :
    (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
      record).mass =
      (((newReset E fieldTail m seed).execute environment Reference state).block record).mass :=
  DensityOperator.basisSlice_mass_of_factor _ (newResetLabel E fieldTail m seed)
    (newReset_block_factor E fieldTail m seed state record)

/-- Zero-probability actual records give the zero Reference operator, with no positive-branch
premise. -/
lemma newResetReferenceCoefficient_zero
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ResetRecord E fieldTail m seed History)
    (zero : (((newReset E fieldTail m seed).execute environment Reference state).block
      record).mass = 0) :
    newResetReferenceCoefficient (environment := environment) E fieldTail m seed state record =
      DensityOperator.zero Reference :=
  (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
    record).eq_zero_of_mass_eq_zero
    ((newResetReferenceCoefficient_mass E fieldTail m seed state record).trans zero)

/-- Summing the actual record masses keeps exactly the arbitrary incoming total mass. -/
lemma newResetReferenceCoefficient_total_mass
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (∑ record : ResetRecord E fieldTail m seed History,
      (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
        record).mass) = state.mass := by
  calc
    _ = ∑ record : ResetRecord E fieldTail m seed History,
        (((newReset E fieldTail m seed).execute environment Reference state).block record).mass :=
      Finset.sum_congr rfl (fun record _ =>
        newResetReferenceCoefficient_mass E fieldTail m seed state record)
    _ = ((newReset E fieldTail m seed).execute environment Reference state).mass := rfl
    _ = state.mass := Circuit.execute_mass (environment := environment) (newReset E fieldTail m
      seed) Reference state

/-- Pointwise scalar factors commute with the complete finite sum in their original order. -/
private lemma sum_record_factors {Index : Type} [Fintype Index]
    {terms coefficients : Index → ℂ} {left right : ℂ}
    (factor : ∀ index, terms index = left * coefficients index * star right) :
    (∑ index, terms index) = left * (∑ index, coefficients index) * star right := by
  calc
    _ = ∑ index, left * coefficients index * star right :=
      Finset.sum_congr rfl (fun index _ => factor index)
    _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]

/-- A fixed complete Store groups only density blocks of its actual separate histories and reset
paths. -/
lemma newReset_store_factor
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal p.size m))
    (left right : (Recovery.Layout.terminal p.size m).register.Index)
    (refLeft refRight : Reference.Index) :
    (∑ history : ClassicalOracleModel.empty.HiddenState ×
        (History × (newReset E fieldTail m seed).Path),
      (((newReset E fieldTail m seed).execute environment Reference state).block
        (stored, history)).matrix (left, refLeft) (right, refRight)) =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) left *
        (∑ history : ClassicalOracleModel.empty.HiddenState ×
            (History × (newReset E fieldTail m seed).Path),
          (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
            (stored, history)).matrix
            refLeft refRight) *
        star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) right) := by
  refine sum_record_factors ?_
  intro history
  exact newReset_record_factor E fieldTail m seed state (stored, history)
    left right refLeft refRight

/-- Any joint Store observation invariant under the real result writes keeps its full Reference
matrix.
The write-invariance premise is a property of the mathematical observer, never of the incoming
State. -/
lemma newReset_weighted_reference
    (weight : Store (Recovery.Layout.terminal p.size m) → ℂ)
    (unchanged : ∀ wire stored value,
      weight (stored.write (newResetCells p m wire) value) = weight stored)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((newReset E fieldTail m seed).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) left right :=
  QuditShift.resetToBasis_weighted_reference (allowAllocation := false)
    (implementations := newResetImplementations p.size m)
    (newResetCells p m) (newResetLabel E fieldTail m seed) state weight unchanged left right

/-- Every unwritten cell observation retains its full weighted Reference matrix through the actual
reset. -/
lemma newReset_read_weighted_reference
    {shape : CShape} (observed : CStorageRef (Recovery.Layout.terminal p.size m) shape)
    (different : (newResetScratch p m).key ≠ observed.key)
    (weight : CShape.Value shape → ℂ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((newReset E fieldTail m seed).execute environment Reference state)
      (fun entry _ => weight (entry.1.read (.storage observed))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (.storage observed))) left right := by
  exact newReset_weighted_reference E fieldTail m seed
    (fun stored => weight (stored.read (.storage observed)))
    (fun wire stored value => congrArg weight
      (Store.read_write_other stored (newResetCells p m wire) observed value
        (by rw [newResetCells_key]; exact different))) state left right

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
