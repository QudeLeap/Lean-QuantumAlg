/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Space
import all QuantumAlg.Components.Classical.Model.BitWord.Random.Space
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Space

/-!
# Independent simultaneous space of the actual single-bank RSA parent

Every preallocated source, complete parameter, packed observation and factor
is live before the first source draw. The sole quantum bank and reusable
measurement cells are then added once. Sampler, complete recovery, full-bank
reset and selection use disjoint chronological scopes, so their additional
space is bounded by a pointwise maximum rather than their sum.

-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := MeasuredRSAModel

/-- Source and parameter cells are already in the frame; only actual sampler scratch is extra. -/
def samplerScratch (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (9 * modulusBits N + 14))

/-- Complete recovery includes its eight real packages and its native modular-power scratch. -/
def recoveryScratch (N : Nat) : SpacePool .quantum :=
  LatticeFixedBatchRecoveryMachine.additionalSpace (model := Model) N

/-- Parallel reset retains one fresh classical measurement bit for each actual bank wire. -/
def bankResetScratch (width : Nat) : SpacePool .quantum :=
  (2 * width + 4) • SpacePool.ofShape (.finite 2)

/-- The final selector reuses exactly its accepted flag, word and unpacked candidate. -/
def selectorScratch (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (2 * modulusBits N + 2))

/-- Separate chronological scratch scopes contribute their maximum on each native axis. -/
def temporarySpace (N : Nat) : SpacePool .quantum :=
  SpacePool.max (samplerScratch N)
    (SpacePool.max (recoveryScratch N)
      (SpacePool.max (bankResetScratch (arithmeticBits N)) (selectorScratch N)))

/-- The actual physical bank contains two words, one control and three clean helper systems. -/
def bankSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout
    (MAU.Multiplication.Gidney.Measured.Physical.qubits (arithmeticBits N)).toQuantum

/-- The same retained binary cells are reused by every member and survive bank restart. -/
def readoutSpace (N : Nat) : SpacePool .quantum :=
  (ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N) +
    (arithmeticBits N - 2)) •
    SpacePool.ofShape (.finite 2)

/-- Every preallocated batch destination, the single bank and readout cells remain live together. -/
def liveSpace (N count : Nat) : SpacePool .quantum :=
  Recycling.ClassicalFrame.frameSpace N count + bankSpace N + readoutSpace N

/-- A parameter-only allowance includes the literal no-bank empty case and full positive peak. -/
def spaceLimit (N : Nat) : Nat → SpacePool .quantum
  | 0 => SpacePool.ofShape (.bits (modulusBits N + 1))
  | laterCount + 1 => liveSpace N (laterCount + 1) + temporarySpace N

-- Keep recovery opaque while checking the pointwise maximum's classical projection.
omit configuration in
private lemma scratchMaximum_classicalBits
    (first second third fourth : SpacePool .quantum) :
    SpacePool.max first (SpacePool.max second (SpacePool.max third fourth)) .classicalBits =
      max (first .classicalBits)
        (max (second .classicalBits) (max (third .classicalBits) (fourth .classicalBits))) := rfl

omit configuration in
private lemma samplerScratch_classicalBits (N : Nat) :
    samplerScratch N .classicalBits = 9 * modulusBits N + 14 := rfl

omit configuration in
private lemma bankResetScratch_classicalBits (width : Nat) :
    bankResetScratch width .classicalBits = 2 * width + 4 := by
  have binaryWidth : CShape.bitWidth (.finite 2) = 1 := by decide
  change (2 * width + 4) • CShape.bitWidth (.finite 2) = _
  simp only [nsmul_eq_mul, binaryWidth, Nat.mul_one, Nat.cast_id]

omit configuration in
private lemma selectorScratch_classicalBits (N : Nat) :
    selectorScratch N .classicalBits = 2 * modulusBits N + 2 := rfl

omit configuration in
/-- The classical scratch coordinate retains every reset bit and every native recovery package. -/
lemma rsaMeasuredParent_temporarySpace_classicalBits (N : Nat) :
    temporarySpace N .classicalBits =
      max (9 * modulusBits N + 14)
        (max (recoveryScratch N .classicalBits)
          (max (2 * arithmeticBits N + 4) (2 * modulusBits N + 2))) := by
  exact (scratchMaximum_classicalBits (samplerScratch N) (recoveryScratch N)
    (bankResetScratch (arithmeticBits N)) (selectorScratch N)).trans
      (congrArg₂ (fun left right : Nat => max left right)
        (samplerScratch_classicalBits N)
        (congrArg (fun remaining : Nat => max (recoveryScratch N .classicalBits) remaining)
          (congrArg₂ (fun left right : Nat => max left right)
            (bankResetScratch_classicalBits (arithmeticBits N))
            (selectorScratch_classicalBits N))))

/-- All preallocated classical capacity and the reusable readout cells are counted simultaneously.
-/
lemma rsaMeasuredParent_liveSpace_classicalBits (N count : Nat) :
    liveSpace N count .classicalBits =
      Recycling.ClassicalFrame.classicalBits N count +
        (measurementBits N + (arithmeticBits N - 2)) := by
  have binaryWidth : CShape.bitWidth (.finite 2) = 1 := by decide
  rw [liveSpace, Recycling.ClassicalFrame.rsaRecyclingFrame_frameSpace_eq]
  change Recycling.ClassicalFrame.classicalBits N count + 0 +
    (ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N) +
    (arithmeticBits N - 2)) •
      CShape.bitWidth (.finite 2) = _
  rw [nsmul_eq_mul, binaryWidth, Nat.mul_one, Nat.add_zero]
  rfl

omit configuration in
private lemma samplerScratch_le (N : Nat) : samplerScratch N ≤ temporarySpace N :=
  SpacePool.le_max_left _ _

omit configuration in
private lemma recoveryScratch_le (N : Nat) : recoveryScratch N ≤ temporarySpace N :=
  (SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)

omit configuration in
private lemma bankResetScratch_le (N : Nat) :
    bankResetScratch (arithmeticBits N) ≤ temporarySpace N :=
  (SpacePool.le_max_left _ _).trans
    ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _))

omit configuration in
private lemma selectorScratch_le (N : Nat) : selectorScratch N ≤ temporarySpace N :=
  (SpacePool.le_max_right _ _).trans
    ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _))

omit configuration in
private lemma sequence_spaces_le {firstCtx middleCtx lastCtx : RuntimeCtx .quantum}
    (first : Circuit Model firstCtx middleCtx) (second : Circuit Model middleCtx lastCtx)
    (path : (first.seq second).Path) (resident auxiliary : SpacePool .quantum)
    (firstBound : first.peakResidentSpace path.1 ≤ resident ∧
      first.peakAuxiliarySpace path.1 ≤ auxiliary)
    (secondBound : second.peakResidentSpace path.2 ≤ resident ∧
      second.peakAuxiliarySpace path.2 ≤ auxiliary) :
    (first.seq second).peakResidentSpace path ≤ resident ∧
      (first.seq second).peakAuxiliarySpace path ≤ auxiliary := by
  constructor
  · exact (Circuit.peakResidentSpace_seq first second path).trans_le
      (SpacePool.max_le firstBound.1 secondBound.1)
  · exact (Circuit.peakAuxiliarySpace_seq first second path).trans_le
      (SpacePool.max_le firstBound.2 secondBound.2)

omit configuration in
private lemma source_spaces {ctx : RuntimeCtx .quantum} (N : Nat)
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N))
    (path : (source N sample parameter).Path) :
    (source N sample parameter).peakResidentSpace path ≤ ctx.residentSpace + samplerScratch N ∧
      (source N sample parameter).peakAuxiliarySpace path ≤
        ctx.auxiliarySpace + samplerScratch N := by
  apply sequence_spaces_le
    (ShorStyle.Canonical.Sampler.PackedSample.draw (model := Model) N sample)
    (ShorStyle.Canonical.Sampler.Program.circuit (model := Model)
      N (FirstAccepted.cellRead sample) parameter) path
  · exact ⟨(BitWord.Random.randomCode_peakResidentSpace (execution := Model) sample path.1).trans_le
         (le_add_of_nonneg_right zero_le),
      (BitWord.Random.randomCode_peakAuxiliarySpace (execution := Model) sample path.1).trans_le
         (le_add_of_nonneg_right zero_le)⟩
  · exact ⟨ShorStyle.Canonical.Sampler.Program.samplerProgram_resident_le
        (model := Model) N (FirstAccepted.cellRead sample) parameter path.2,
      ShorStyle.Canonical.Sampler.Program.samplerProgram_auxiliary_le
        (model := Model) N (FirstAccepted.cellRead sample) parameter path.2⟩

omit configuration in
private lemma round_spaces (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width : Nat) {shape : CShape}
    (parameter : CInputRef (ShortDLP.CompiledMAU.Recycling.Measured.context
      frame frameNoQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (ShortDLP.CompiledMAU.Recycling.Measured.context
      frame frameNoQuantum m ell width) (.bits (ShortDLP.CompiledMAU.Recycling.resultBits m ell)))
    (path : (ShortDLP.CompiledMAU.Recycling.Measured.Round.code
      frame frameNoQuantum m ell width parameter wide modulus generator target result).Path) :
    (ShortDLP.CompiledMAU.Recycling.Measured.Round.code
      frame frameNoQuantum m ell width
      parameter wide modulus generator target result).peakResidentSpace path ≤
      (ShortDLP.CompiledMAU.Recycling.Measured.context
        frame frameNoQuantum m ell width).residentSpace + bankResetScratch width ∧
    (ShortDLP.CompiledMAU.Recycling.Measured.Round.code
      frame frameNoQuantum m ell width
      parameter wide modulus generator target result).peakAuxiliarySpace path ≤
      (ShortDLP.CompiledMAU.Recycling.Measured.context
        frame frameNoQuantum m ell width).auxiliarySpace + bankResetScratch width := by
  have resident := ShortDLP.CompiledMAU.Recycling.Measured.Round.measuredRound_resident
    frame frameNoQuantum m ell width parameter wide modulus generator target result path
  have auxiliary := ShortDLP.CompiledMAU.Recycling.Measured.Round.measuredRound_auxiliary
    frame frameNoQuantum m ell width parameter wide modulus generator target result path
  exact ⟨resident.trans_le (add_comm _ _).le, auxiliary.trans_le (add_comm _ _).le⟩

omit configuration in
private lemma prepare_spaces (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width N : Nat)
    (path : (ShortDLP.CompiledMAU.Recycling.Measured.prepare frame frameNoQuantum m ell width
    N).Path) :
    (ShortDLP.CompiledMAU.Recycling.Measured.prepare frame frameNoQuantum m ell width
    N).peakResidentSpace
      path ≤ (ShortDLP.CompiledMAU.Recycling.Measured.context
        frame frameNoQuantum m ell width).residentSpace ∧
      (ShortDLP.CompiledMAU.Recycling.Measured.prepare frame frameNoQuantum m ell width
    N).peakAuxiliarySpace
        path ≤ (ShortDLP.CompiledMAU.Recycling.Measured.context
          frame frameNoQuantum m ell width).auxiliarySpace := by
  let bank : Circuit Model frame
      (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width) :=
    Circuit.prepareZero frame frame.canonicalFreshKey
      (MAU.Multiplication.Gidney.Measured.Physical.qubits width).toQuantum
      frame.runtimeCtx_canonicalFreshKey_fresh
      (ShortDLP.CompiledMAU.Recycling.Measured.preparationDisjoint frame frameNoQuantum width)
  let cells := MeasurementCells.allocate (model := Model)
    (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width)
    2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2))
  let loaded := Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
    (classicalOracles := .empty)
    (ShortDLP.CompiledMAU.Recycling.Measured.load frame frameNoQuantum m ell width N)
  have bankResident := MeasurementCells.context_residentSpace_mono
    (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width) 2
    (Nat.zero_le (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2)))
  have bankAuxiliary := MeasurementCells.context_auxiliarySpace_mono
    (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width) 2
    (Nat.zero_le (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2)))
  have bankBound : bank.peakResidentSpace path.1 ≤
      (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).residentSpace ∧
      bank.peakAuxiliarySpace path.1 ≤
        (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).auxiliarySpace :=
    ⟨(Circuit.prepare_peakResidentSpace frame frame.canonicalFreshKey
        (MAU.Multiplication.Gidney.Measured.Physical.qubits width).toQuantum
        frame.runtimeCtx_canonicalFreshKey_fresh
        (ShortDLP.CompiledMAU.Recycling.Measured.preparationDisjoint frame frameNoQuantum width)
        path.1).trans_le bankResident,
      (Circuit.prepare_peakAuxiliarySpace frame frame.canonicalFreshKey
        (MAU.Multiplication.Gidney.Measured.Physical.qubits width).toQuantum
        frame.runtimeCtx_canonicalFreshKey_fresh
        (ShortDLP.CompiledMAU.Recycling.Measured.preparationDisjoint frame frameNoQuantum width)
        path.1).trans_le bankAuxiliary⟩
  have cellsBound : cells.peakResidentSpace path.2.1 ≤
      (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).residentSpace ∧
      cells.peakAuxiliarySpace path.2.1 ≤
        (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).auxiliarySpace :=
    ⟨MeasurementCells.allocate_peakResidentSpace (model := Model)
        (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width)
        2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2)) path.2.1,
      MeasurementCells.allocate_peakAuxiliarySpace (model := Model)
        (ShortDLP.CompiledMAU.Recycling.Measured.bankContext frame frameNoQuantum width)
        2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2)) path.2.1⟩
  have loadedBound : loaded.peakResidentSpace path.2.2 ≤
      (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).residentSpace ∧
      loaded.peakAuxiliarySpace path.2.2 ≤
        (ShortDLP.CompiledMAU.Recycling.Measured.context frame frameNoQuantum m ell
    width).auxiliarySpace :=
    ⟨(Circuit.peakResidentSpace_unitary
        (ShortDLP.CompiledMAU.Recycling.Measured.load frame frameNoQuantum m ell width N)
    path.2.2).le,
      (Circuit.peakAuxiliarySpace_unitary
        (ShortDLP.CompiledMAU.Recycling.Measured.load frame frameNoQuantum m ell width N)
    path.2.2).le⟩
  exact sequence_spaces_le bank (cells.seq loaded) path _ _ bankBound
    (sequence_spaces_le cells loaded path.2 _ _ cellsBound loadedBound)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

omit configuration in
private lemma measured_context_auxiliary (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width : Nat) :
    (ShortDLP.CompiledMAU.Recycling.Measured.context
      frame frameNoQuantum m ell width).auxiliarySpace =
      (ShortDLP.CompiledMAU.Recycling.resultBits m ell + (width - 2)) •
        SpacePool.ofShape (.finite 2) +
      (SpacePool.ofQuantumLayout
        (MAU.Multiplication.Gidney.Measured.Physical.qubits width).toQuantum +
          frame.auxiliarySpace) := by
  rw [ShortDLP.CompiledMAU.Recycling.Measured.context, MeasurementCells.context_auxiliarySpace]
  rfl

private lemma readyContext_spaces (count : Nat) :
    (readyContext base noQuantum N count).residentSpace =
        liveSpace N count + base.residentSpace ∧
      (readyContext base noQuantum N count).auxiliarySpace =
        liveSpace N count + base.auxiliarySpace := by
  constructor
  · rw [readyContext, ShortDLP.CompiledMAU.Recycling.Measured.context_resident,
      Recycling.ClassicalFrame.rsaRecyclingFrame_context_resident]
    unfold liveSpace bankSpace readoutSpace
    ac_rfl
  · rw [readyContext, measured_context_auxiliary,
      Recycling.ClassicalFrame.rsaRecyclingFrame_context_auxiliary]
    unfold liveSpace bankSpace readoutSpace
    ac_rfl

private lemma frame_ready_le (count : Nat) :
    (Recycling.ClassicalFrame.context base N count).residentSpace ≤
        (readyContext base noQuantum N count).residentSpace ∧
      (Recycling.ClassicalFrame.context base N count).auxiliarySpace ≤
        (readyContext base noQuantum N count).auxiliarySpace := by
  constructor
  · rw [readyContext, ShortDLP.CompiledMAU.Recycling.Measured.context_resident]
    have bank : (Recycling.ClassicalFrame.context base N count).residentSpace ≤
        bankSpace N + (Recycling.ClassicalFrame.context base N count).residentSpace :=
      le_add_of_nonneg_left zero_le
    exact bank.trans (le_add_of_nonneg_left zero_le)
  · rw [readyContext, measured_context_auxiliary]
    have bank : (Recycling.ClassicalFrame.context base N count).auxiliarySpace ≤
        bankSpace N + (Recycling.ClassicalFrame.context base N count).auxiliarySpace :=
      le_add_of_nonneg_left zero_le
    exact bank.trans (le_add_of_nonneg_left zero_le)

private lemma firstSource_spaces (laterCount : Nat)
    (path : (firstSource base N laterCount).Path) :
    (firstSource base N laterCount).peakResidentSpace path ≤
        (readyContext base noQuantum N (laterCount + 1)).residentSpace + temporarySpace N ∧
      (firstSource base N laterCount).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N (laterCount + 1)).auxiliarySpace + temporarySpace N := by
  have sourceBound := source_spaces N
    (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0) path
  have frame := frame_ready_le base noQuantum N (laterCount + 1)
  exact ⟨sourceBound.1.trans (add_le_add frame.1 (samplerScratch_le N)),
    sourceBound.2.trans (add_le_add frame.2 (samplerScratch_le N))⟩

private lemma nextSource_spaces (count : Nat) (batch : Fin count)
    (path : (nextSource base noQuantum N count batch).Path) :
    (nextSource base noQuantum N count batch).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (nextSource base noQuantum N count batch).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N := by
  have sourceBound := source_spaces N
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.sampleRef base N count batch))
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)) path
  exact ⟨sourceBound.1.trans (add_le_add le_rfl (samplerScratch_le N)),
    sourceBound.2.trans (add_le_add le_rfl (samplerScratch_le N))⟩

private lemma member_spaces (input : Input N) (count : Nat) (batch : Fin count) (index : Fin
    membersPerBatch)
    (path : (member base noQuantum N input count batch index).Path) :
    (member base noQuantum N input count batch index).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (member base noQuantum N input count batch index).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N := by
  have bound := round_spaces (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (measuredRSA_arithmeticBits_atLeastTwo input) (modulusWord N)
    (parameterGenerator N) (parameterTargetWord N)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.packedRef base N count batch index)) path
  exact ⟨bound.1.trans (add_le_add le_rfl (bankResetScratch_le N)),
    bound.2.trans (add_le_add le_rfl (bankResetScratch_le N))⟩

private lemma members_spaces (input : Input N) (count : Nat) (batch : Fin count)
    (path : (members base noQuantum N input count batch).Path) :
    (members base noQuantum N input count batch).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (members base noQuantum N input count batch).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N := by
  constructor
  · exact Circuit.forRange_resident_le membersPerBatch (member base noQuantum N input count batch)
      ((readyContext base noQuantum N count).residentSpace + temporarySpace N)
      (le_add_of_nonneg_right zero_le)
      (fun index selected => (member_spaces base noQuantum N input count batch index
    selected).1) path
  · exact Circuit.forRange_auxiliary_le membersPerBatch (member base noQuantum N input count batch)
      ((readyContext base noQuantum N count).auxiliarySpace + temporarySpace N)
      (le_add_of_nonneg_right zero_le)
      (fun index selected => (member_spaces base noQuantum N input count batch index
    selected).2) path

private lemma recover_spaces (input : Input N) (count : Nat) (batch : Fin count)
    (path : (recover base noQuantum N input count batch).Path) :
    (recover base noQuantum N input count batch).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (recover base noQuantum N input count batch).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N := by
  have resident := LatticeFixedBatchRecoveryMachine.into_resident_le (model := Model) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.factorRef base N count batch))
    path
  have auxiliary := LatticeFixedBatchRecoveryMachine.into_auxiliary_le (model := Model) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.factorRef base N count batch))
    path
  exact ⟨resident.trans ((add_le_add (recoveryScratch_le N) le_rfl).trans_eq
       (add_comm _ _)),
    auxiliary.trans ((add_le_add (recoveryScratch_le N) le_rfl).trans_eq (add_comm _ _))⟩

private lemma batchBody_spaces (input : Input N) (count : Nat) (batch : Fin count)
    (path : (batchBody base noQuantum N input count batch).Path) :
    (batchBody base noQuantum N input count batch).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (batchBody base noQuantum N input count batch).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N :=
  sequence_spaces_le (members base noQuantum N input count batch)
    (recover base noQuantum N input count batch) path _ _
    (members_spaces base noQuantum N input count batch path.1)
    (recover_spaces base noQuantum N input count batch path.2)

private lemma nextBatch_spaces (input : Input N) (count : Nat) (batch : Fin count)
    (path : (nextBatch base noQuantum N input count batch).Path) :
    (nextBatch base noQuantum N input count batch).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (nextBatch base noQuantum N input count batch).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N :=
  sequence_spaces_le (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) path _ _
    (nextSource_spaces base noQuantum N count batch path.1)
    (batchBody_spaces base noQuantum N input count batch path.2)

private lemma select_spaces (count : Nat)
    (path : (select base noQuantum N count).Path) :
    (select base noQuantum N count).peakResidentSpace path ≤
        (readyContext base noQuantum N count).residentSpace + temporarySpace N ∧
      (select base noQuantum N count).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N count).auxiliarySpace + temporarySpace N := by
  have resident := FirstAccepted.Direct.Optional.Allocation.into_resident_le (model := Model)
    (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)) path
  have auxiliary := FirstAccepted.Direct.Optional.Allocation.into_auxiliary_le (model := Model)
    (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)) path
  exact ⟨resident.trans (add_le_add le_rfl (selectorScratch_le N)),
    auxiliary.trans (add_le_add le_rfl (selectorScratch_le N))⟩

/-- Every positive path includes the simultaneous frame, one bank and maximum actual scratch. -/
lemma rsaMeasuredParent_positiveCode_spaces_le (input : Input N) (laterCount : Nat)
    (path : (positiveCode base noQuantum N input laterCount).Path) :
    (positiveCode base noQuantum N input laterCount).peakResidentSpace path ≤
        (readyContext base noQuantum N (laterCount + 1)).residentSpace + temporarySpace N ∧
      (positiveCode base noQuantum N input laterCount).peakAuxiliarySpace path ≤
        (readyContext base noQuantum N (laterCount + 1)).auxiliarySpace + temporarySpace N := by
  have frame := frame_ready_le base noQuantum N (laterCount + 1)
  have allocationResident := Recycling.ClassicalFrame.rsaRecyclingFrame_allocate_resident
    base N (laterCount + 1) path.1
  have allocationAuxiliary := Recycling.ClassicalFrame.rsaRecyclingFrame_allocate_auxiliary
    base N (laterCount + 1) path.1
  have allocation :
      (Recycling.ClassicalFrame.allocate base N (laterCount + 1)).peakResidentSpace path.1 ≤
          (readyContext base noQuantum N (laterCount + 1)).residentSpace + temporarySpace N ∧
        (Recycling.ClassicalFrame.allocate base N (laterCount + 1)).peakAuxiliarySpace path.1 ≤
          (readyContext base noQuantum N (laterCount + 1)).auxiliarySpace + temporarySpace N :=
    ⟨allocationResident.trans_le
        ((Recycling.ClassicalFrame.rsaRecyclingFrame_context_resident base N (laterCount +
    1)).symm.le.trans
           (frame.1.trans (le_add_of_nonneg_right zero_le))),
      allocationAuxiliary.trans_le
        ((Recycling.ClassicalFrame.rsaRecyclingFrame_context_auxiliary base N (laterCount +
    1)).symm.le.trans
           (frame.2.trans (le_add_of_nonneg_right zero_le)))⟩
  have first := firstSource_spaces base noQuantum N laterCount path.2.1
  have initial := prepare_spaces (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat path.2.2.1
  have initialBound :=
    And.intro (initial.1.trans (le_add_of_nonneg_right (show 0 ≤ temporarySpace N from zero_le)))
      (initial.2.trans (le_add_of_nonneg_right (show 0 ≤ temporarySpace N from zero_le)))
  have firstBatch := batchBody_spaces base noQuantum N input (laterCount + 1) 0 path.2.2.2.1
  have tailResident := Circuit.forRange_resident_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    ((readyContext base noQuantum N (laterCount + 1)).residentSpace + temporarySpace N)
    (le_add_of_nonneg_right zero_le)
    (fun index selected =>
      (nextBatch_spaces base noQuantum N input (laterCount + 1) index.succ selected).1)
    path.2.2.2.2.1
  have tailAuxiliary := Circuit.forRange_auxiliary_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    ((readyContext base noQuantum N (laterCount + 1)).auxiliarySpace + temporarySpace N)
    (le_add_of_nonneg_right zero_le)
    (fun index selected =>
      (nextBatch_spaces base noQuantum N input (laterCount + 1) index.succ selected).2)
    path.2.2.2.2.1
  have last := select_spaces base noQuantum N (laterCount + 1) path.2.2.2.2.2
  let tail := Circuit.forRange laterCount fun index =>
    nextBatch base noQuantum N input (laterCount + 1) index.succ
  let final := select base noQuantum N (laterCount + 1)
  let body := batchBody base noQuantum N input (laterCount + 1) 0
  let prepared := ShortDLP.CompiledMAU.Recycling.Measured.prepare
    (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat
  let source := firstSource base N laterCount
  let allocated := Recycling.ClassicalFrame.allocate base N (laterCount + 1)
  have tailBound := sequence_spaces_le tail final path.2.2.2.2 _ _
    ⟨tailResident, tailAuxiliary⟩ last
  have bodyBound := sequence_spaces_le body (tail.seq final) path.2.2.2 _ _
    firstBatch tailBound
  have preparedBound := sequence_spaces_le prepared (body.seq (tail.seq final))
    path.2.2 _ _ initialBound bodyBound
  have sourceBound := sequence_spaces_le source
    (prepared.seq (body.seq (tail.seq final))) path.2 _ _ first preparedBound
  exact sequence_spaces_le allocated
    (source.seq (prepared.seq (body.seq (tail.seq final)))) path _ _ allocation sourceBound

/-- The same actual run preserves all original resident resources under an independent allowance.
-/
lemma rsaMeasuredParent_run_resident_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakResidentSpace path ≤
      base.residentSpace + spaceLimit N count := by
  cases count with
  | zero => exact (NativeRetryEmpty.code_resident base N path).le
  | succ laterCount =>
      have bound := rsaMeasuredParent_positiveCode_spaces_le
        base noQuantum N input laterCount path
      refine bound.1.trans_eq ?_
      rw [(readyContext_spaces base noQuantum N (laterCount + 1)).1]
      change liveSpace N (laterCount + 1) + base.residentSpace + temporarySpace N =
        base.residentSpace + (liveSpace N (laterCount + 1) + temporarySpace N)
      ac_rfl

/-- The same paths retain every original auxiliary role and count all actual temporary capacity. -/
lemma rsaMeasuredParent_run_auxiliary_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakAuxiliarySpace path ≤
      base.auxiliarySpace + spaceLimit N count := by
  cases count with
  | zero => exact (NativeRetryEmpty.code_auxiliary base N path).le
  | succ laterCount =>
      have bound := rsaMeasuredParent_positiveCode_spaces_le
        base noQuantum N input laterCount path
      refine bound.2.trans_eq ?_
      rw [(readyContext_spaces base noQuantum N (laterCount + 1)).2]
      change liveSpace N (laterCount + 1) + base.auxiliarySpace + temporarySpace N =
        base.auxiliarySpace + (liveSpace N (laterCount + 1) + temporarySpace N)
      ac_rfl

end

end QuantumAlg.Factoring.RSA.Measured.Program
