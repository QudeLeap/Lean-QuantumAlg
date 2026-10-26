/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prepared
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Point

/-!
# Preparation support through the actual full-bank restart

The actual reset writes only finite outcome cells;
the native loader preserves every classical read. The same four constants and
both complete row families therefore remain supported on every positive
returned block, with all incoming History, HiddenState and Reference retained.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open Sampling.Storage Sampling.Locality

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma prepared_write_finite_iff (sampler : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (before : Store ctx) {cardinality : ℕ+}
    (output : CWriteRef ctx (.finite cardinality)) (value : CShape.Value (.finite cardinality)) :
    Prepared sampler I (before.write output value) ↔ Prepared sampler I before := by
  have words {width : Nat} (cell : CStorageRef ctx (.unsignedWord width)) :
      (before.write output value).read (.storage cell) = before.read (.storage cell) :=
    Store.read_write_other before output cell value
      (Driver.write_shape_key_ne output cell (by intro impossible; cases impossible))
  have arrays (cell : CStorageRef ctx (.fixedVector 34 (.unsignedWord 256))) :
      (before.write output value).read (.storage cell) = before.read (.storage cell) :=
    Store.read_write_other before output cell value
      (Driver.write_shape_key_ne output cell (by intro impossible; cases impossible))
  constructor
  · exact prepared_of_reads sampler I (before.write output value) before
      (fun cell _ => (words cell).symm)
      (arrays sampler.frame.x.toCStorageRef).symm (arrays sampler.frame.y.toCStorageRef).symm
  · exact prepared_of_reads sampler I before (before.write output value)
      (fun cell _ => words cell)
      (arrays sampler.frame.x.toCStorageRef) (arrays sampler.frame.y.toCStorageRef)

private lemma reset_one_selects_prepared (cleanup : Cleanup.Parameters ctx)
    (wire : Fin ctx.systemCount) (sampler : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (fun store => decide (Prepared sampler I store)) true
      (cleanup.one wire) environment := by
  intro Reference History _ state
  refine instrument_select_read (services := services)
    (Reference := Reference) (History := History)
    (resetOneInstrument cleanup wire environment)
    (fun store => decide (Prepared sampler I store)) ?_ true state
  intro store outcome
  exact decide_eq_decide.mpr
    (prepared_write_finite_iff sampler I store (cleanup.outputAt wire) (.finite outcome))

private lemma reset_range_selects_prepared (cleanup : Cleanup.Parameters ctx)
    (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (sampler : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (fun store => decide (Prepared sampler I store)) true
      (cleanup.run count wires) environment := by
  apply selects_read_range
  intro index
  exact reset_one_selects_prepared cleanup (wires index) sampler I environment

private lemma restart_selects_prepared (original : Sampling.Storage.Inputs ctx)
    (sampler : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (output : CWriteRef ctx (.finite 2))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    SelectsRead (fun store => decide (Prepared sampler I store)) true
      (original.restart output) environment := by
  dsimp only [Inputs.restart, Cleanup.Parameters.prepared, Cleanup.Parameters.circuit]
  apply selects_read_identity_embed
  apply selects_read_seq
  · exact reset_range_selects_prepared (ctx := ctx) (services := services)
      _ ctx.systemCount id sampler I environment
  · exact selects_read_unitary (ctx := ctx) (services := services)
      (operations := BitWord.model) (environment := environment)
      (fun store => decide (Prepared sampler I store)) true _

/-- Every positive actual restart block retains the same preparation invariant. -/
lemma restart_preserves_prepared (original : Sampling.Storage.Inputs ctx)
    (sampler : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (output : CWriteRef ctx (.finite 2))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass → Prepared sampler I entry.1) :
    ∀ entry, 0 < (((original.restart (services := services) output).execute
      environment Reference state).block entry).mass → Prepared sampler I entry.1 := by
  have actual := selects_read_preserves_positive
    (fun store => decide (Prepared sampler I store)) true (original.restart output) environment
    (restart_selects_prepared original sampler I output environment) state
    (fun entry positive => by simpa only [decide_eq_true_eq] using supported entry positive)
  intro entry positive
  exact of_decide_eq_true (actual entry positive)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
