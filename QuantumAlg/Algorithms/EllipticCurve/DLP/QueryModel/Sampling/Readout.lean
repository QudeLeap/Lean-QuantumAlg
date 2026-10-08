/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Laws
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Actual retained ECDLP readout with complete store and reference entries

Distinct live result keys receive their named exponent-qubit values. The
terminal execution retains every point-register coordinate, final store and
external-reference matrix entry in the actual measurement fiber equation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The real writes selected by one full basis label, retaining every other storage key. -/
@[expose] public def writtenStore (I : ECDLPInstance E) (A : Access I)
    (stored : Store (post I)) (basis : (post I).register.Index) : Store (post I) :=
  Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := model I A)
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts I) stored
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := model I A)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I) basis)

/-- Both full labels agree exactly at the two actually measured exponent registers. -/
@[expose] public def readoutsAgree (I : ECDLPInstance E)
    (left right : (post I).register.Index) : Prop :=
  ∀ index : Fin (sampleWidth I),
    left (exponentPosition I index) = right (exponentPosition I index)

private theorem labelsAgree_iff (ctx : RuntimeCtx .quantum) (items : List (ZReadout ctx))
    (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree items left right ↔
      ∀ item ∈ items, left item.wire = right item.wire := by
  induction items with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail ih => simp [Circuit.measurementLabelsAgree, ih]

private theorem readouts_agree (I : ECDLPInstance E)
    (left right : (post I).register.Index) :
    Circuit.measurementLabelsAgree (readouts I) left right ↔ readoutsAgree I left right := by
  rw [labelsAgree_iff]
  constructor
  · intro agrees index
    exact agrees (readout I index) (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro agrees item present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact agrees index

/-- A scalar observation of the original state, selecting the actual complete-store write fiber. -/
public def readoutEntry (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (post I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) : ℂ :=
  ExecutionState.weightedMatrixEntry state
    (fun original => if writtenStore I A original.1 left = stored then 1 else 0)
    (left, leftRef) (right, rightRef)

/-- Every measured exponent qubit writes its own distinct retained cell. -/
public theorem readouts_nodup (I : ECDLPInstance E) :
    ((readouts I).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  change (readout I left).output.key = (readout I right).output.key at same
  rw [readout, readout, QubitReadouts.readout_key, QubitReadouts.readout_key] at same
  exact MeasurementCells.reference_key_injective (bankContext I) 2 (sampleWidth I) same

/-- The actual sequential writes retain the exact value of each original exponent qubit. -/
public theorem measured_cell (I : ECDLPInstance E) (A : Access I)
    (stored : Store (post I)) (basis : (post I).register.Index)
    (index : Fin (sampleWidth I)) :
    ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := model I A)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I) stored
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := model I A)
        (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
        (readouts I) basis)).read (.storage (cell I index).toCStorageRef)).toFin.val =
      (basis (exponentPosition I index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (gates := AlgorithmGate.model)
    (oracles := model I A) (operations := BitWord.model) (services := ClassicalOracleModel.empty)
    (readouts I) (readouts_nodup I) (readout I index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) stored basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  simp only [readout, QubitReadouts.readout] at numeric
  rw [QubitReadouts.outputAt_read] at numeric
  exact numeric

/-- Each final complete store has exactly its actual quantum-reference measurement fiber. -/
public theorem readoutCode_store_entry (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (post I) Reference ((executionModel I A).HiddenState × History))
    (stored : Store (post I)) (left right : (post I).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((readoutCode I A).execute Reference state).mapClassical
      (fun record => record.1)).block stored).matrix
        (left, leftRef) (right, rightRef) =
      if readoutsAgree I left right then
        readoutEntry I A state stored left right leftRef rightRef
      else 0 := by
  rw [BasisSeeded.store_matrix]
  have actual := Circuit.measurementSequence_store_matrix_entry
    (gates := AlgorithmGate.model) (oracles := model I A)
    (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
    (readouts I) state stored left right leftRef rightRef
  rw [readouts_agree] at actual
  exact actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
