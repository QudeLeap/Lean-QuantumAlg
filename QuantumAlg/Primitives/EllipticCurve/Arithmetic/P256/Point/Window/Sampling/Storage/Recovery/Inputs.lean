/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Point

/-!
# Original arithmetic-input support through the complete actual preparation

The original modulus, constants and complete base arrays survive the real
restart and all measured windows. Every Boolean property of any such
stored value therefore remains supported on all positive returned blocks.
The input predicate is supplied by the original initialization and retained
by the same actual execution, with arbitrary History and Reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution Locality

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def originalStorageRead {shape : CShape} (observed : CStorageRef ctx shape)
    (predicate : CShape.Value shape → Bool) (store : Store ctx) : Bool :=
  predicate (store.read (.storage observed))

private lemma reset_selects_storage (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount) {shape : CShape}
    (observed : CStorageRef ctx shape) (predicate : CShape.Value shape → Bool) (flag : Bool)
    (different : ∀ cardinality : ℕ+, CShape.finite cardinality ≠ shape)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (originalStorageRead observed predicate) flag
      (parameters.run count wires) environment := by
  apply selects_read_range
  intro index Reference History _ state
  apply instrument_select_read (resetOneInstrument parameters (wires index) environment)
  intro store outcome
  exact congrArg predicate (Store.read_write_other store
    (parameters.outputAt (wires index)) observed (.finite outcome)
    (write_shape_key_ne _ observed (different _)))

private lemma middle_selects_storage (parameters : Parameters ctx) (index : WindowIndex)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (predicate : CShape.Value shape → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (preserved : NamedMiddlePreservesRead parameters index environment observed) :
    SelectsRead (originalStorageRead observed predicate) flag
      (parameters.measuredMiddle index) environment := by
  intro Reference History _ state
  let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
    parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  apply recordedInstrument_select_read (namedMeasuredMiddleInstrument parameters index environment)
  intro original outcomes
  exact congrArg predicate (preserved original outcomes)

private lemma block_selects_storage (parameters : Parameters ctx) (index : WindowIndex)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (predicate : CShape.Value shape → Bool) (flag : Bool)
    (different : ∀ cardinality : ℕ+, CShape.finite cardinality ≠ shape)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (preserved : NamedMiddlePreservesRead parameters index environment observed) :
    SelectsRead (originalStorageRead observed predicate) flag
      (parameters.block index) environment := by
  apply selects_read_seq
  · apply selects_read_identity_embed
    exact reset_selects_storage parameters.resetParameters _ _ observed predicate flag
      different environment
  · apply selects_read_seq
    · exact selects_read_unitary _ _ _
    · exact middle_selects_storage parameters index observed predicate flag environment preserved

private lemma sequence_selects_original_read (parameters : Parameters ctx)
    (indices : List WindowIndex) (read : Store ctx → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (each : ∀ index, SelectsRead read flag (parameters.block index) environment) :
    SelectsRead read flag (parameters.sequence indices) environment := by
  induction indices with
  | nil => exact selects_read_id _ _
  | cons index indices inductionHypothesis =>
      exact selects_read_seq _ _ _ _ (each index) inductionHypothesis

private lemma preparation_selects_storage (original : Inputs ctx) (sampler : Parameters ctx)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (predicate : CShape.Value shape → Bool) (flag : Bool)
    (different : ∀ cardinality : ℕ+, CShape.finite cardinality ≠ shape)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (preserved : ∀ index, NamedMiddlePreservesRead sampler index environment observed) :
    SelectsRead (originalStorageRead observed predicate) flag
      (original.preparation sampler) environment := by
  unfold Inputs.preparation
  apply selects_read_seq
  · dsimp only [Inputs.restart, Cleanup.Parameters.prepared, Cleanup.Parameters.circuit]
    apply selects_read_identity_embed
    apply selects_read_seq
    · exact reset_selects_storage _ ctx.systemCount id observed predicate flag different environment
    · exact selects_read_unitary _ _ _
  · exact sequence_selects_original_read sampler schedule _ flag environment
      (fun index => block_selects_storage sampler index observed predicate flag different
        environment (preserved index))

private def arrayPairRead {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Bool)
    (store : Store ctx) : Bool :=
  predicate (store.read (.storage first)) (store.read (.storage second))

private lemma reset_selects_array_pair (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount) {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (arrayPairRead first second predicate) flag
      (parameters.run count wires) environment := by
  apply selects_read_range
  intro index Reference History _ state
  apply instrument_select_read (resetOneInstrument parameters (wires index) environment)
  intro store outcome
  exact congrArg₂ predicate
    (Store.read_write_other store (parameters.outputAt (wires index)) first
      (.finite outcome) (write_shape_key_ne _ first (by intro impossible; cases impossible)))
    (Store.read_write_other store (parameters.outputAt (wires index)) second
      (.finite outcome) (write_shape_key_ne _ second (by intro impossible; cases impossible)))

private lemma middle_selects_array_pair (parameters : Parameters ctx) (index : WindowIndex)
    {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (arrayPairRead first second predicate) flag
      (parameters.measuredMiddle index) environment := by
  intro Reference History _ state
  let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
    parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  apply recordedInstrument_select_read (namedMeasuredMiddleInstrument parameters index environment)
  intro original outcomes
  exact congrArg₂ predicate
    (namedMeasuredMiddle_array_read parameters index environment first original outcomes)
    (namedMeasuredMiddle_array_read parameters index environment second original outcomes)

private lemma preparation_selects_array_pair (original : Inputs ctx) (sampler : Parameters ctx)
    {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (arrayPairRead first second predicate) flag
      (original.preparation sampler) environment := by
  unfold Inputs.preparation
  apply selects_read_seq
  · dsimp only [Inputs.restart, Cleanup.Parameters.prepared, Cleanup.Parameters.circuit]
    apply selects_read_identity_embed
    apply selects_read_seq
    · exact reset_selects_array_pair _ ctx.systemCount id first second predicate flag environment
    · exact selects_read_unitary _ _ _
  · apply sequence_selects_original_read sampler schedule _ flag environment
    intro index
    apply selects_read_seq
    · apply selects_read_identity_embed
      exact reset_selects_array_pair sampler.resetParameters _ _ first second predicate flag
        environment
    · apply selects_read_seq
      · exact selects_read_unitary _ _ _
      · exact middle_selects_array_pair sampler index first second predicate flag environment

namespace Inputs

/-- Every supported property of an original modulus or input constant survives preparation. -/
lemma preparation_word_support (original : Inputs ctx) (sampler : Parameters ctx)
    {width : Nat} (observed : CStorageRef ctx (.unsignedWord width))
    (originalWord : observed.key ∈ frameInputKeys sampler.frame)
    (predicate : CShape.Value (.unsignedWord width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag) :
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag := by
  apply selects_read_preserves_positive (originalStorageRead observed predicate) flag
    (original.preparation sampler) environment _ state supported
  exact preparation_selects_storage original sampler observed predicate flag
    (by intro cardinality impossible; cases impossible) environment
    (fun index => namedMeasuredMiddle_frame_word_read sampler index environment
      observed originalWord)

/-- Every supported property of an entire original base array survives all actual windows. -/
lemma preparation_array_support (original : Inputs ctx) (sampler : Parameters ctx)
    {width length : Nat} (observed : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag) :
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag := by
  apply selects_read_preserves_positive (originalStorageRead observed predicate) flag
    (original.preparation sampler) environment _ state supported
  exact preparation_selects_storage original sampler observed predicate flag
    (by intro cardinality impossible; cases impossible) environment
    (fun index => namedMeasuredMiddle_array_read sampler index environment observed)

/-- Joint properties of the two original coordinate arrays survive on each positive block. -/
lemma preparation_array_pair_support (original : Inputs ctx) (sampler : Parameters ctx)
    {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (predicate : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      predicate (entry.1.read (.storage first)) (entry.1.read (.storage second)) = flag) :
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      predicate (entry.1.read (.storage first)) (entry.1.read (.storage second)) = flag := by
  exact selects_read_preserves_positive (arrayPairRead first second predicate) flag
    (original.preparation sampler) environment
    (preparation_selects_array_pair original sampler first second predicate flag environment)
    state supported

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
