/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named.Read
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Original input reads survive each actual source stage

The real zero reset retains every caller input outside its reused result cell.
The actual point and Fourier records retain the four loaded constants and both
complete row arrays, so no preparation is repeated between windows.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.WindowTables
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Cleanup.Parameters

/-- The complete real zero-reset record preserves every separated original read. -/
lemma zeroRunRecord_read (parameters : Cleanup.Parameters ctx)
    (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (before : Store ctx) {shape : CShape} (input : CInputRef ctx shape)
    (free : parameters.output.key ∉ input.storageKeys) :
    (parameters.zeroRunRecord (services := services) count wires before).1.read input =
      before.read input := by
  unfold zeroRunRecord
  exact Circuit.forRangeStoreRecord_invariant
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (allowAllocation := false) count (fun index => parameters.one (wires index))
    (fun index => parameters.zeroOneRecord (wires index))
    (fun (_ : Nat) (store : Store ctx) => store.read input = before.read input)
    (by
      intro bit current preserved
      exact (Store.read_write_of_not_mem_storageKeys current
        (parameters.outputAt (wires bit)) (.finite 0) input (by
          simpa only [outputAt, QubitReadouts.outputAt_key] using free)).trans preserved)
    before rfl

end Cleanup.Parameters

namespace Sampling

attribute [local irreducible] Driver.namedDriverInstrument Locality.namedMeasuredMiddleInstrument

private lemma row_read_of_array_read {width length : Nat}
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (first last : Store ctx)
    (same : first.read (.storage array.toCStorageRef) = last.read (.storage array.toCStorageRef))
    (row : Fin length) : first.read (rowRead array row) = last.read (rowRead array row) := by
  exact congrArg (fun value => value.get row) same

private lemma driverInputValues_of_reads {width : Nat}
    (frame : Outer.Frame ctx width) (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    (before after : Store ctx)
    (words : ∀ {bits : Nat} (cell : CStorageRef ctx (.unsignedWord bits)),
      cell.key ∈ Driver.frameInputKeys frame →
      after.read (.storage cell) = before.read (.storage cell))
    (x : after.read (.storage frame.x.toCStorageRef) =
      before.read (.storage frame.x.toCStorageRef))
    (y : after.read (.storage frame.y.toCStorageRef) =
      before.read (.storage frame.y.toCStorageRef))
    (values : Driver.driverInputValues frame curve point row before) :
    Driver.driverInputValues frame curve point row after := by
  have modulusRead := words frame.modulus.toCStorageRef
    (by simp only [Driver.frameInputKeys, List.mem_cons, true_or])
  have zeroRead := words frame.zero.toCStorageRef
    (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true])
  have oneRead := words frame.one.toCStorageRef
    (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true])
  have curveRead := words frame.curveA.toCStorageRef
    (by simp only [Driver.frameInputKeys, List.mem_cons, true_or, or_true])
  dsimp only [Driver.driverInputValues, Driver.driverReadValues,
    ClassicalRoutines.Modular.NativePower.wordRead] at values ⊢
  rw [modulusRead, zeroRead, oneRead, curveRead,
    row_read_of_array_read frame.x _ _ x row,
    row_read_of_array_read frame.y _ _ y row]
  exact values

/-- The actual zero-reset Store retains every original Fourier result. -/
lemma reset_zero_result_read (parameters : Parameters ctx) (index : WindowIndex)
    (before : Store ctx) (position : BitPosition 260) :
    (parameters.resetParameters.zeroRunRecord (services := services)
      (index.lowerWidth + 1) (parameters.wire index) before).1.read
        (.storage (parameters.results.cells position).toCStorageRef) =
      before.read (.storage (parameters.results.cells position).toCStorageRef) := by
  apply Cleanup.Parameters.zeroRunRecord_read
  simpa only [CInputRef.storageKeys, List.mem_singleton, Parameters.resetParameters] using
    parameters.output_separate 0 position

/-- The actual zero-reset Store retains all six original driver input reads. -/
lemma reset_zero_driverInputValues (parameters : Parameters ctx) (index : WindowIndex)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
    (before : Store ctx)
    (values : Driver.driverInputValues parameters.frame curve point row before) :
    Driver.driverInputValues parameters.frame curve point row
      (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) before).1 := by
  have words : ∀ {width : Nat} (cell : CWriteRef ctx (.unsignedWord width)),
      (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) before).1.read
          (.storage cell.toCStorageRef) = before.read (.storage cell.toCStorageRef) := by
    intro width cell
    apply Cleanup.Parameters.zeroRunRecord_read
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      Driver.write_shape_key_ne parameters.resetParameters.output cell.toCStorageRef
        (by intro impossible; cases impossible)
  have arrays : ∀ (cell : CWriteRef ctx (.fixedVector 34 (.unsignedWord 256))),
      (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) before).1.read
          (.storage cell.toCStorageRef) = before.read (.storage cell.toCStorageRef) := by
    intro cell
    apply Cleanup.Parameters.zeroRunRecord_read
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      Driver.write_shape_key_ne parameters.resetParameters.output cell.toCStorageRef
        (by intro impossible; cases impossible)
  dsimp only [Driver.driverInputValues, Driver.driverReadValues,
    ClassicalRoutines.Modular.NativePower.wordRead] at values ⊢
  rw [words parameters.frame.modulus, words parameters.frame.zero,
    words parameters.frame.one, words parameters.frame.curveA,
    row_read_of_array_read parameters.frame.x _ _ (arrays parameters.frame.x) row,
    row_read_of_array_read parameters.frame.y _ _ (arrays parameters.frame.y) row]
  exact values

/-- Every actual measured-middle record retains a complete current row input predicate. -/
lemma named_middle_driverInputValues (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34) :
    let chosen := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype chosen.1 := chosen.2.1
    ∀ (original : Store ctx × services.HiddenState)
      (outcome : chosen.1 × Bits (index.lowerWidth + 1)),
      Driver.driverInputValues parameters.frame curve point row original.1 →
      Driver.driverInputValues parameters.frame curve point row
        ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
          original outcome).1.1 := by
  let chosen := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype chosen.1 := chosen.2.1
  dsimp only
  intro original outcome values
  have words : ∀ {width : Nat} (cell : CStorageRef ctx (.unsignedWord width)),
      cell.key ∈ Driver.frameInputKeys parameters.frame →
      ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
        original outcome).1.1.read (.storage cell) = original.1.read (.storage cell) := by
    intro width cell member
    exact Locality.namedMeasuredMiddle_frame_word_read parameters index environment
      cell member original outcome
  have x := Locality.namedMeasuredMiddle_array_read parameters index environment
    parameters.frame.x.toCStorageRef original outcome
  have y := Locality.namedMeasuredMiddle_array_read parameters index environment
    parameters.frame.y.toCStorageRef original outcome
  exact driverInputValues_of_reads parameters.frame curve point row original.1 _
    words x y values

end Sampling

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
