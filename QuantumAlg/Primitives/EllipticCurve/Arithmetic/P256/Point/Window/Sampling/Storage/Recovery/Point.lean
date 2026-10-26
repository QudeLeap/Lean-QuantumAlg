/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Protection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named.Read.Point

/-!
# Original point support through the complete actual preparation

The same complete stored point survives real reset, H preparation, each
constructed-table point operation and the actual Fourier readout. The
full-bank restart and fixed affine loader preserve it as well. Selection
covariance therefore retains any originally supported point property on
every positive returned block, with arbitrary History and Reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution Locality

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def nominalPointRead {width : Nat}
    (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (store : Store ctx) : Bool :=
  predicate (store.read (.storage observed))

private lemma reset_selects_point (parameters : Cleanup.Parameters ctx) (count : Nat)
    (wires : Fin count → Fin ctx.systemCount) {width : Nat}
    (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (parameters.run count wires) environment := by
  apply selects_read_range
  intro index Reference History _ state
  apply instrument_select_read (resetOneInstrument parameters (wires index) environment)
  intro store outcome
  exact congrArg predicate (Store.read_write_other store
    (parameters.outputAt (wires index)) observed (.finite outcome)
    (write_shape_key_ne _ observed (by intro impossible; cases impossible)))

private lemma middle_selects_point (parameters : Parameters ctx) (index : WindowIndex)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (parameters.measuredMiddle index) environment := by
  intro Reference History _ state
  let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
    parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  apply recordedInstrument_select_read (namedMeasuredMiddleInstrument parameters index environment)
  intro original outcomes
  exact congrArg predicate
    (namedMeasuredMiddle_point_read parameters index environment observed original outcomes)

private lemma block_selects_point (parameters : Parameters ctx) (index : WindowIndex)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (parameters.block index) environment := by
  apply selects_read_seq
  · apply selects_read_identity_embed
    exact reset_selects_point parameters.resetParameters _ _ observed predicate flag environment
  · apply selects_read_seq
    · exact selects_read_unitary _ _ _
    · exact middle_selects_point parameters index observed predicate flag environment

private lemma sequence_selects_point (parameters : Parameters ctx) (indices : List WindowIndex)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (parameters.sequence indices) environment := by
  induction indices with
  | nil => exact selects_read_id _ _
  | cons index indices inductionHypothesis =>
      exact selects_read_seq _ _ _ _
        (block_selects_point parameters index observed predicate flag environment)
        inductionHypothesis

private lemma restart_selects_point (original : Inputs ctx)
    (output : CWriteRef ctx (.finite 2)) {width : Nat}
    (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (original.restart output) environment := by
  dsimp only [Inputs.restart, Cleanup.Parameters.prepared, Cleanup.Parameters.circuit]
  apply selects_read_identity_embed
  apply selects_read_seq
  · exact reset_selects_point _ ctx.systemCount id observed predicate flag environment
  · exact selects_read_unitary _ _ _

private lemma select_eq_self_of_positive {Label : Type} [Fintype Label] {R : Register}
    (state : ExecutionState Label R) (read : Label → Bool) (flag : Bool)
    (supported : ∀ entry, 0 < (state.block entry).mass → read entry = flag) :
    state.selectClassical read flag = state := by
  apply ExecutionState.ext
  intro entry
  rw [ExecutionState.selectClassical_block]
  by_cases positive : 0 < (state.block entry).mass
  · rw [supported entry positive, if_pos rfl]
  · have zeroMass : (state.block entry).mass = 0 :=
      le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    rw [state.block_eq_zero_of_mass_eq_zero entry zeroMass]
    exact ite_self _

private lemma selects_read_preserves_positive {allocation : Bool} (read : Store ctx → Bool)
    (flag : Bool)
    (program : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx allocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (selected : SelectsRead read flag program environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass → read entry.1 = flag) :
    ∀ entry, 0 < ((program.execute environment Reference state).block entry).mass →
      read entry.1 = flag := by
  have same := selected state
  rw [select_eq_self_of_positive state (fun entry => read entry.1) flag supported] at same
  intro entry positive
  apply ExecutionState.selectClassical_read_eq_of_block_ne_zero
    (program.execute environment Reference state) (fun current => read current.1) flag entry
  rw [← same]
  intro zero
  rw [zero, DensityOperator.zero_mass] at positive
  exact (lt_irrefl 0) positive

namespace Inputs

/-- The actual restart and entire sampler commute with any original nominal-point selection. -/
lemma preparation_selects_point (original : Inputs ctx) (sampler : Parameters ctx)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (nominalPointRead observed predicate) flag
      (original.preparation sampler) environment := by
  unfold preparation
  apply selects_read_seq
  · exact restart_selects_point original _ observed predicate flag environment
  · exact sequence_selects_point sampler schedule observed predicate flag environment

/-- Every positive output block retains an originally supported property of the same point cell. -/
lemma preparation_point_support (original : Inputs ctx) (sampler : Parameters ctx)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (predicate : CShape.Value (.ellipticCurvePoint width) → Bool) (flag : Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag) :
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      predicate (entry.1.read (.storage observed)) = flag := by
  exact selects_read_preserves_positive (nominalPointRead observed predicate) flag
    (original.preparation sampler) environment
    (original.preparation_selects_point sampler observed predicate flag environment) state supported

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
