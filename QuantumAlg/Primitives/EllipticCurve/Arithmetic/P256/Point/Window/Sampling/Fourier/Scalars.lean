/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Read
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Prefix
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Store

/-!
# Original recorded cells determine each actual window's Fourier phase

The same named point instrument preserves all original Fourier results.
Its following real readout preserves every past result and writes exactly
the current outcome. The native feedback scalar therefore uses the same
incoming stored prefix. These record laws impose no arithmetic domain or
point-action premise, and change no circuit, path or physical coordinate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma storedPrefix_eq_of_past_reads {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (before after : Store ctx)
    (same : ∀ previous : BitPosition totalBits, ports.past previous →
      after.read (.storage (ports.results previous).toCStorageRef) =
        before.read (.storage (ports.results previous).toCStorageRef)) :
    Feedback.storedPrefix ports after = Feedback.storedPrefix ports before := by
  apply tupleCoordinates_injective ports.start
  funext previous
  rw [Feedback.window_storedPrefix_coordinate, Feedback.window_storedPrefix_coordinate]
  have startBound : ports.start ≤ totalBits :=
    (Nat.le_add_right ports.start active).trans ports.within
  let position : Fin totalBits := ⟨previous.val, previous.isLt.trans_le startBound⟩
  have past : ports.past (ports.stream, position) := ⟨rfl, previous.isLt⟩
  exact congrArg CShape.Value.toFin (same (ports.stream, position) past)

private def RecordedFeedbackScalar {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (before after : Store ctx)
    (basis : ctx.register.Index) : Prop :=
  Feedback.wordScalar ports after basis (List.finRange active) =
    Partner.phaseBasis active
      (Partner.suffixPhases true ports.start active (fun _ => 1)
        (Feedback.storedPrefix ports before))
      (bankCoordinates ports.wires ports.qubits basis).1

private lemma recordedFeedbackScalar_of_prefix {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (before after : Store ctx)
    (basis : ctx.register.Index)
    (same : Feedback.storedPrefix ports after = Feedback.storedPrefix ports before) :
    RecordedFeedbackScalar ports before after basis := by
  unfold RecordedFeedbackScalar
  rw [Feedback.window_feedback_scalar_phaseBasis]
  have phases : Feedback.priorPhases ports after =
      Partner.suffixPhases true ports.start active (fun _ => 1)
        (Feedback.storedPrefix ports before) := by
    funext current
    rw [← Feedback.window_priorPhases_suffix, same]
  rw [phases]

attribute [local irreducible] RecordedFeedbackScalar

namespace Parameters

variable (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

/-- Every past original cell survives the actual point and corrected Fourier readout. -/
lemma named_middle_past_read (previous : BitPosition 260)
    (past : (parameters.ports index).past previous) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
        original outcomes).1.1.read
          (.storage (parameters.results.cells previous).toCStorageRef) =
        original.1.read (.storage (parameters.results.cells previous).toCStorageRef) := by
  dsimp only
  intro original outcomes
  rw [Locality.namedMeasuredMiddle_record]
  dsimp only
  rw [inverseStoreRecord_store]
  exact (window_outcomeStore_past_read (parameters.ports index) _ outcomes.2 previous past).trans
    (Driver.namedDriverInstrument_result_read parameters index previous environment
      original outcomes.1)

/-- Each current original cell contains precisely its own actual Fourier outcome bit. -/
lemma named_middle_current_bit (bit : Fin (index.lowerWidth + 1)) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      (((Locality.namedMeasuredMiddleInstrument parameters index environment).record
        original outcomes).1.1.read
          (.storage ((parameters.ports index).output bit).toCStorageRef)).toFin =
        tupleCoordinates (index.lowerWidth + 1) outcomes.2 bit := by
  dsimp only
  intro original outcomes
  rw [Locality.namedMeasuredMiddle_record]
  dsimp only
  rw [inverseStoreRecord_store]
  exact Fin.ext (window_outcomeStore_binary_read (parameters.ports index) _ outcomes.2 bit)

/-- The point's real returned Store retains the exact incoming same-stream prefix. -/
lemma named_point_storedPrefix :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original outcome,
      Feedback.storedPrefix (parameters.ports index)
          (point.2.2.record original outcome).1.1 =
        Feedback.storedPrefix (parameters.ports index) original.1 := by
  dsimp only
  intro original outcome
  apply storedPrefix_eq_of_past_reads
  intro previous _
  exact Driver.namedDriverInstrument_result_read parameters index previous environment
    original outcome

/-- The real native feedback reads the original prefix through the point's actual Store. -/
lemma named_point_feedback_scalar :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original outcome (basis : ctx.register.Index),
      RecordedFeedbackScalar (parameters.ports index) original.1
        (point.2.2.record original outcome).1.1 basis := by
  dsimp only
  intro original outcome basis
  exact recordedFeedbackScalar_of_prefix (parameters.ports index) original.1 _ basis
    (parameters.named_point_storedPrefix index environment original outcome)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
