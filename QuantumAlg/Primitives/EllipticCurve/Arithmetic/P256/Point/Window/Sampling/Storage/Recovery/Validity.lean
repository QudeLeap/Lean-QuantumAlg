/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Range
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Conditional
import all QuantumAlg.Core.Execution.Circuit.Support.Sequence

/-! # Bounded selected words through the actual restart, sampler and nearest checker -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
namespace Storage

open Execution Locality Driver ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

noncomputable section
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma middle_scalar_read (sampler : Parameters ctx) (index : WindowIndex)
    (observed : CStorageRef ctx (.unsignedWord 260))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    NamedMiddlePreservesRead sampler index environment observed := by
  apply namedMeasuredMiddle_read_of_point
  · apply namedDriverInstrument_read_separate
      (sampler.pointParameters index) sampler.frame sampler.modulus index.row environment observed
    · intro key written
      simp only [frameWorkKeys, List.mem_cons, List.not_mem_nil, or_false] at written
      rcases written with rfl | rfl | rfl | rfl
      all_goals exact write_shape_key_ne _ observed (by decide)
    · exact fun _ => write_shape_key_ne _ observed (by intro same; cases same)
    · exact write_shape_key_ne _ observed (by intro same; cases same)
    · exact fun _ => write_shape_key_ne _ observed (by intro same; cases same)
    · exact write_shape_key_ne _ observed (by intro same; cases same)
  · exact fun _ => write_shape_key_ne _ observed (by intro same; cases same)

namespace Inputs

private def PreparationSelectedLtStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Parameters ctx)
    (selected : CWriteRef ctx (.unsignedWord 260))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage selected.toCStorageRef)).toNat < original.order.modulus),
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage selected.toCStorageRef)).toNat < original.order.modulus

private lemma preparation_selected_lt : PreparationSelectedLtStatement := by
  intro ctx services original sampler selected environment Reference History _ state supported
  have preserved : SelectsRead
      (originalStorageRead selected.toCStorageRef
        (fun value => decide (value.toNat < original.order.modulus))) true
      (original.preparation sampler) environment :=
    preparation_selects_storage original sampler selected.toCStorageRef
    (fun value => decide (value.toNat < original.order.modulus)) true
    (by intro cardinality impossible; cases impossible) environment
    (fun index => middle_scalar_read sampler index selected.toCStorageRef environment)
  have positive := selects_read_preserves_positive
    (originalStorageRead selected.toCStorageRef
      (fun value => decide (value.toNat < original.order.modulus))) true
    (original.preparation sampler) environment preserved state
    (fun entry mass => decide_eq_true (supported entry mass))
  intro entry mass
  exact of_decide_eq_true (positive entry mass)

/-- The actual explicit-seven checker keeps the selected scalar below the same order. -/
lemma checkerStore_selected_lt (original : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx × services.HiddenState)
    (distinct : checkers.keys.Nodup)
    (prior : (before.1.read (.storage checkers.selected.toCStorageRef)).toNat <
      original.order.modulus) :
    ((original.checkerStore sampler checkers environment before).read
      (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus :=
  Nearest.attemptStore_selected_lt (environment := environment)
    original.curve original.order (Recovery.pairedInput sampler) original.base original.target
    checkers.inverseSuccess checkers.candidate checkers.reconstruction checkers.scalarResult
    checkers.targetAccepted checkers.accepted checkers.selected before.1 before.2 distinct prior

private def CheckerSelectedLtStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (_distinct : checkers.keys.Nodup)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus),
    ∀ entry, 0 < ((((original.checkerTail sampler checkers).code (services := services)).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus

private lemma checker_selected_lt : CheckerSelectedLtStatement := by
  intro ctx services original sampler checkers environment distinct Reference History _
    state supported
  obtain ⟨record, execute, returned⟩ := original.checker_actualRecord sampler checkers environment
  rw [execute]
  apply Conditional.mapped_supported
  · exact supported
  · intro entry prior
    change ((record (entry.1, entry.2.1)).1.1.read
      (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus
    rw [returned]
    exact checkerStore_selected_lt original sampler checkers environment
      (entry.1, entry.2.1) distinct prior

private def AttemptSelectedLtStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (_distinct : checkers.keys.Nodup)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus),
    ∀ entry, 0 < (((original.attempt sampler checkers).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus

private lemma attemptSelectedLtStatement_proof : AttemptSelectedLtStatement := by
  intro ctx services original sampler checkers environment distinct Reference History _
    state supported
  rw [original.attempt_code_eq sampler checkers]
  apply Circuit.supported_store_seq environment (original.preparation sampler)
    ((original.checkerTail sampler checkers).code (services := services)) Reference state
    (fun store => (store.read (.storage checkers.selected.toCStorageRef)).toNat <
      original.order.modulus)
  apply checker_selected_lt (ctx := ctx) (services := services)
    original sampler checkers environment distinct (Reference := Reference)
    (History := History × (original.preparation (services := services) sampler).Path)
    ((original.preparation (services := services) sampler).execute environment Reference state)
  exact preparation_selected_lt (ctx := ctx) (services := services) original sampler
    checkers.selected environment (Reference := Reference) (History := History) state supported

/-- Every positive block of the actual complete attempt retains a bounded selected scalar. -/
lemma attempt_selected_lt (original : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (distinct : checkers.keys.Nodup)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus) :
    ∀ entry, 0 < (((original.attempt sampler checkers).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < original.order.modulus := by
  exact attemptSelectedLtStatement_proof (ctx := ctx) (services := services)
    original sampler checkers environment distinct (Reference := Reference) (History := History)
    state supported

end Inputs
end
end Storage
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
