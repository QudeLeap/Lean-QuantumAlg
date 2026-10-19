/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Frame

/-!
# Original raw recovery observations and actual candidate acceptance

The actual five stages accept precisely the natural scalar equation and the
two flags of the original raw-recovery model. The candidate is read from that
model, including its failure value, and is not supplied as an additional
correctness premise. Structural separation concerns only the five caller
destinations and the original point inputs. Actual persistent allocation can
discharge these layout conditions internally.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

omit [BitWord.Selected model] in
private lemma exposure_reads (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx)
    (value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape scalarWidth)))
    (candidateInverse : candidate.key ≠ inverseSuccess.key)
    (reconstructionInverse : reconstruction.key ≠ inverseSuccess.key)
    (reconstructionCandidate : reconstruction.key ≠ candidate.key) :
    let after := FiniteCyclicDLP.RawRecovery.Native.exposureWrite
      inverseSuccess candidate reconstruction before value
    after.read (.storage inverseSuccess.toCStorageRef) = value.first ∧
      after.read (.storage candidate.toCStorageRef) = value.second.first ∧
      after.read (.storage reconstruction.toCStorageRef) = value.second.second := by
  dsimp only
  unfold FiniteCyclicDLP.RawRecovery.Native.exposureWrite
  constructor
  · rw [Store.read_write_other _ reconstruction inverseSuccess.toCStorageRef
      value.second.second reconstructionInverse]
    rw [Store.read_write_other _ candidate inverseSuccess.toCStorageRef
      value.second.first candidateInverse, Store.read_write_same]
  constructor
  · rw [Store.read_write_other _ reconstruction candidate.toCStorageRef
      value.second.second reconstructionCandidate, Store.read_write_same]
  · exact Store.read_write_same _ _ _

/-- Every structural caller read outside the five actual destinations is unchanged. -/
lemma recoveryStore_preserves_read (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx) (hidden : model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key, accepted.key], key ∉ observed.storageKeys) :
    (recoveryStore (environment := environment) curve modulus sample base target inverseSuccess
      candidate reconstruction
      scalarResult accepted (before, hidden)).read observed = before.read observed := by
  rw [recoveryStore_eq]
  rw [verifyStep_preserves_read _ _ _ _ _ _ _ _ _ _ observed
    (free scalarResult.key (by simp)) (free accepted.key (by simp))]
  exact FiniteCyclicDLP.RawRecovery.Native.exposureWrite_read_other
    inverseSuccess candidate reconstruction before _ observed
    (free inverseSuccess.key (by simp)) (free candidate.key (by simp))
    (free reconstruction.key (by simp))

/-- Verification preserves all three exact raw-recovery observations on distinct destinations. -/
lemma recoveryStore_observations (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx) (hidden : model.HiddenState)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key, accepted.key].Nodup) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
    let after := recoveryStore (environment := environment) curve modulus sample base target
      inverseSuccess candidate
      reconstruction scalarResult accepted (before, hidden)
    after.read (.storage inverseSuccess.toCStorageRef) = raw.first ∧
      after.read (.storage candidate.toCStorageRef) = raw.second.first ∧
      after.read (.storage reconstruction.toCStorageRef) = raw.second.second := by
  let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
    (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
  have reads := exposure_reads inverseSuccess candidate reconstruction before raw
    (by intro equality; simp [equality] at distinct)
    (by intro equality; simp [equality] at distinct)
    (by intro equality; simp [equality] at distinct)
  have preserved {shape : CShape} (observed : CInputRef ctx shape)
      (scalarFree : scalarResult.key ∉ observed.storageKeys)
      (acceptedFree : accepted.key ∉ observed.storageKeys) :
      (recoveryStore (environment := environment) curve modulus sample base target
        inverseSuccess candidate reconstruction
        scalarResult accepted (before, hidden)).read observed =
        (FiniteCyclicDLP.RawRecovery.Native.exposureWrite inverseSuccess candidate reconstruction
          before raw).read observed := by
    rw [recoveryStore_eq]
    exact verifyStep_preserves_read curve (.storage candidate.toCStorageRef) base target
      (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
      scalarResult accepted _ _ observed scalarFree acceptedFree
  dsimp only
  constructor
  · exact (preserved (.storage inverseSuccess.toCStorageRef)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show scalarResult.key ≠ inverseSuccess.key from
          by intro equality; simp [equality] at distinct))
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show accepted.key ≠ inverseSuccess.key from
          by intro equality; simp [equality] at distinct))).trans reads.1
  constructor
  · exact (preserved (.storage candidate.toCStorageRef)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show scalarResult.key ≠ candidate.key from
          by intro equality; simp [equality] at distinct))
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show accepted.key ≠ candidate.key from
          by intro equality; simp [equality] at distinct))).trans reads.2.1
  · exact (preserved (.storage reconstruction.toCStorageRef)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show scalarResult.key ≠ reconstruction.key from
          by intro equality; simp [equality] at distinct))
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
        (show accepted.key ≠ reconstruction.key from
          by intro equality; simp [equality] at distinct))).trans reads.2.2

/-- Actual five-stage acceptance is exactly the original recovered scalar and both flags. -/
lemma recoveryStore_accepts_iff (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx) (hidden : model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve (before.read base) basePoint)
    (targetRep : PointRepresents curve (before.read target) targetPoint)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key, accepted.key].Nodup)
    (baseFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ base.storageKeys)
    (targetFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ target.storageKeys) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
    ((recoveryStore (environment := environment) curve modulus sample base target inverseSuccess
      candidate reconstruction
      scalarResult accepted (before, hidden)).read
        (.storage accepted.toCStorageRef)).toBool = true ↔
      raw.second.first.toNat • basePoint = targetPoint ∧
        raw.first.toBool = true ∧ raw.second.second.toBool = true := by
  let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
    (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
  let recovered := FiniteCyclicDLP.RawRecovery.Native.exposureWrite
    inverseSuccess candidate reconstruction before raw
  let scalar : ClassicalAlgorithms.Word scalarWidth :=
    ⟨raw.second.first.toNat, raw.second.first.toNat_lt⟩
  have scalarValue : raw.second.first = .unsignedWord scalar := by
    cases value : raw.second.first with
    | unsignedWord word =>
        change CShape.Value.unsignedWord word = .unsignedWord
          ⟨raw.second.first.toNat, raw.second.first.toNat_lt⟩
        simp only [value, CShape.Value.toNat]
  have reads := exposure_reads inverseSuccess candidate reconstruction before raw
    (by intro equality; simp [equality] at distinct)
    (by intro equality; simp [equality] at distinct)
    (by intro equality; simp [equality] at distinct)
  have rawBase : recovered.read base = before.read base :=
    FiniteCyclicDLP.RawRecovery.Native.exposureWrite_read_other
      inverseSuccess candidate reconstruction before raw base
      (baseFree inverseSuccess.key (by simp)) (baseFree candidate.key (by simp))
      (baseFree reconstruction.key (by simp))
  have rawTarget : recovered.read target = before.read target :=
    FiniteCyclicDLP.RawRecovery.Native.exposureWrite_read_other
      inverseSuccess candidate reconstruction before raw target
      (targetFree inverseSuccess.key (by simp)) (targetFree candidate.key (by simp))
      (targetFree reconstruction.key (by simp))
  let rawHidden : model.HiddenState :=
    (Classical.choose
      (FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord (environment := environment)
        modulus sample inverseSuccess candidate reconstruction) (before, hidden)).1.2
  have actual := verifyStep_accepts_iff (environment := environment)
    curve (.storage candidate.toCStorageRef) base target
    (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
    scalarResult accepted recovered rawHidden scalar basePoint targetPoint
    (reads.2.1.trans scalarValue)
    (by rw [rawBase]; exact baseRep) (by rw [rawTarget]; exact targetRep)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (show scalarResult.key ≠ candidate.key from
        by intro equality; simp [equality] at distinct))
    (baseFree scalarResult.key (by simp)) (targetFree scalarResult.key (by simp))
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (show scalarResult.key ≠ inverseSuccess.key from
        by intro equality; simp [equality] at distinct))
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (show scalarResult.key ≠ reconstruction.key from
        by intro equality; simp [equality] at distinct))
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (show accepted.key ≠ inverseSuccess.key from
        by intro equality; simp [equality] at distinct))
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (show accepted.key ≠ reconstruction.key from
        by intro equality; simp [equality] at distinct))
  rw [reads.1, reads.2.2] at actual
  rw [recoveryStore_eq]
  exact actual

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
