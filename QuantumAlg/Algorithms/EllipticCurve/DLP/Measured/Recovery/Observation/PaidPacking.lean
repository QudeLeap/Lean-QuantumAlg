/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Coordinates
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Decode.Resources

/-!
# Actual paid decoding of the reversed physical streaming result positions

The input references read the reversed positions inside each chronological block. They
are supplied to the existing literal finite-bit packing and big-endian decoder. The
complete caller Store and arbitrary external Reference remain in the actual execution
equation. The original lexical packed cell, native packing event, decoder events and
peak classical storage are charged. This owner does not prove complete ECC recovery or
success.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PaidPacking

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.ClassicalRoutines
open QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open ActualFeedback
open Recovery.Stage.PointCoordinates

local instance {α : Type} : DecidableEq α := Classical.decEq α

private abbrev Model : ExecutionModel :=
  .quantum AlgorithmGate.model .empty BitWord.model .empty

variable {environment : Model.Environment}

/-- Reverse each physical block independently, retaining the first-then-second order. -/
def reversePosition (m : Nat) (index : Fin (2 * m)) : Fin (2 * m) :=
  Fin.cast (Nat.two_mul m).symm
    (finSumFinEquiv (Sum.map Fin.rev Fin.rev
      (finSumFinEquiv.symm (Fin.cast (Nat.two_mul m) index))))

/-- The actual canonical input at a block position reads that block's reversed physical cell. -/
lemma reversePosition_position {m : Nat} (second : Bool) (current : Fin m) :
    reversePosition m (position second current) = position second current.rev := by
  cases second <;>
    simp [reversePosition, position, StageWord.blockIndex, -Fin.natAdd_eq_addNat]

/-- Structural references supplied to the paid packing instruction, without rewriting any Store. -/
def input (width m : Nat) :
    CInputRef (Recovery.Layout.terminal width m) (.fixedVector (2 * m) (.finite 2)) :=
  .fixedVector fun index =>
    .storage (Recovery.Layout.resultCell width m (reversePosition m index)).toCStorageRef

/-- Every reference reads its actual measured outcome from the complete final Store. -/
lemma input_get (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final)
    (second : Bool) (current : Fin m) :
    (final.read (input width m)).get (position second current) =
      .finite (ReadoutRows.outcomeBit width m (path (position second current.rev)).2.1) := by
  change final.read (.storage
    (Recovery.Layout.resultCell width m (reversePosition m (position second
      current))).toCStorageRef) = _
  rw [reversePosition_position]
  exact FeedbackReads.full_trace_final_read width m path original final valid _

/-- The paid instruction's actual input is the complete-source canonical frequency bit vector. -/
lemma input_frequency_get (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final)
    (second : Bool) (current : Fin m) :
    (final.read (input width m)).get (position second current) =
      .finite (finTwoEquiv.symm
        (ExceptionalOffsetAveraging.pairedBigEndianSelected m
          (pathFrequency width m path) (position second current))) := by
  rw [input_get width m path original final valid,
    pathFrequency_selected_position, Equiv.symm_apply_apply]

/-- The actual containing caller passes these same named references to native recovery. -/
def callerInput {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx) :
    CInputRef ctx (.fixedVector (2 * m) (.finite 2)) :=
  placement.input (input width m)

/-- Full caller reads commute with the real complete-Store placement; no frame is erased. -/
lemma callerInput_read {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx) (stored : Store ctx) :
    stored.read (callerInput placement) =
      ((placement.store stored).1).read (input width m) := by
  have same := placement.contextEmbedding_input_read
    (placement.store stored).1 (placement.store stored).2 (input width m)
  simpa only [callerInput, Prod.mk.eta, Equiv.symm_apply_apply] using same

/-- Existing native recovery code, including its lexical packed cell and release. -/
def code {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m))) : Circuit Model ctx ctx :=
  measuredDecodeInto (model := Model) (callerInput placement) decoded

/-- Actual execution keeps every caller Store, hidden record, path and reference block. -/
lemma code_execute {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (Model.HiddenState × History)) :
    (code placement decoded).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := measuredDecodeStep (model := Model)
          (callerInput placement) decoded entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  measuredDecodeInto_execute (model := Model) (callerInput placement) decoded Reference state

/-- The literal first native event is the paid packing instruction, including at width zero. -/
lemma code_eventTrace {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m)))
    (path : (code placement decoded).Path) :
    (code placement decoded).eventTrace path =
      measuredPackEvent (model := Model) (2 * m) ::
        (TerminalDecode.into (model := Model) .bigEndian
          (packedInput ctx (2 * m))
          (writeUnderDecode decoded (2 * m))).eventTrace path.2 :=
  measuredDecodeInto_eventTrace (model := Model) (callerInput placement) decoded path

/-- Both the literal packing and all decoder instructions remain in the native allowance. -/
lemma code_resourcePool_le {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m)))
    (path : (code placement decoded).Path) :
    (code placement decoded).resourcePool path ≤
      measuredDecodeEnvelope (model := Model) (2 * m) :=
  measuredDecodeInto_resourcePool_le (model := Model) (callerInput placement) decoded path

/-- Serial duration charges the pack before every shift and selected increment. -/
lemma code_depth_le {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m)))
    (duration : Resource.Event Model → Nat) (path : (code placement decoded).Path) :
    (code placement decoded).depth duration path ≤
      duration (measuredPackEvent (model := Model) (2 * m)) + (2 * m) *
        (duration (TerminalDecode.shiftEvent (model := Model) (2 * m)) +
          duration (TerminalDecode.incrementEvent (model := Model) (2 * m))) :=
  measuredDecodeInto_depth_le (model := Model) (callerInput placement) decoded duration path

/-- Resident peak counts the real packed word together with the complete caller context. -/
lemma code_resident {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m)))
    (path : (code placement decoded).Path) :
    (code placement decoded).peakResidentSpace path =
      SpacePool.ofShape (.bits (2 * m)) + ctx.residentSpace :=
  measuredDecodeInto_resident (model := Model) (callerInput placement) decoded path

/-- Auxiliary peak counts the same lexical packed word, which is released on return. -/
lemma code_auxiliary {width m : Nat} {ctx : RuntimeCtx .quantum}
    (placement : ContextEmbedding (Recovery.Layout.terminal width m) ctx)
    (decoded : CWriteRef ctx (.unsignedWord (2 * m)))
    (path : (code placement decoded).Path) :
    (code placement decoded).peakAuxiliarySpace path =
      SpacePool.ofShape (.bits (2 * m)) + ctx.auxiliarySpace :=
  measuredDecodeInto_auxiliary (model := Model) (callerInput placement) decoded path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PaidPacking
