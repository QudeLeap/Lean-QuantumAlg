/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.StructuredWitness
import all QuantumAlg.Primitives.MAU.Inversion.MK.Correction
import all QuantumAlg.Primitives.MAU.Inversion.MK.Correction.Resource

/-!
# Exact inversion resources
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MK
open MK.Correction
open Nat.FixedWidth
open NumberTheory.BinaryGCD

namespace Resource

/-! ## One exact compute/add/uncompute gate schedule and resources -/

/-- Complete fixed compute/correct/add/uncompute gate schedule. -/
def inversionGates (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    List (EncodedBit.GateSpec (Correction.encoding tail counterWidth)) :=
  let fixed := fixedComputeGates tail counterWidth comparisonIndex workIndex
  let correction := correctionComputeGates tail counterWidth p hpOdd
  let targetAdd := stagedTargetAddGates tail counterWidth p
  fixed ++ correction ++ targetAdd ++ correction.reverse ++ fixed.reverse

/-- Compile the exact inversion gate schedule into its physical circuit. -/
def inversionProgram (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Correction.encoding tail counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (inversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- Folded action of the complete inversion gate schedule. -/
def inversionStep (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    Correction.Registers tail counterWidth ->
      Correction.Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (inversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- The complete actual inversion circuit realizes its full gate list. -/
lemma inversionProgram_realizes (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    UnitaryCircuit.Realizes (Correction.encoding tail counterWidth)
      (inversionProgram tail counterWidth p comparisonIndex workIndex hpOdd) environment
      (inversionStep tail counterWidth p comparisonIndex workIndex hpOdd) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (inversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- Complete scale-removing inversion gate schedule. -/
def unscaledInversionGates (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    List (EncodedBit.GateSpec (Correction.encoding tail counterWidth)) :=
  let scaleUnit := montgomeryScaleUnit p tail.succ hpOdd
  let fixed := fixedComputeGates tail counterWidth comparisonIndex workIndex
  let correction := correctionComputeGates tail counterWidth p hpOdd
  let unscale := liftedUnitMultiplicationGates tail counterWidth p scaleUnit⁻¹
  let targetAdd := stagedTargetAddGates tail counterWidth p
  let rescale := liftedUnitMultiplicationGates tail counterWidth p scaleUnit
  fixed ++ correction ++ unscale ++ targetAdd ++ rescale ++
    correction.reverse ++ fixed.reverse

/-- Compile the exact scale-removing inversion gate schedule. -/
def unscaledInversionProgram (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Correction.encoding tail counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (unscaledInversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- Folded action of the complete scale-removing inversion gate schedule. -/
def unscaledInversionStep (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    Correction.Registers tail counterWidth ->
      Correction.Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (unscaledInversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- The complete actual unscaled-inversion circuit realizes its full gate list. -/
lemma unscaledInversionProgram_realizes (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    UnitaryCircuit.Realizes (Correction.encoding tail counterWidth)
      (unscaledInversionProgram tail counterWidth p comparisonIndex workIndex hpOdd) environment
      (unscaledInversionStep tail counterWidth p comparisonIndex workIndex hpOdd) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (unscaledInversionGates tail counterWidth p comparisonIndex workIndex hpOdd)

/-- Width-only primitive-leaf bound for the complete scale-removing inversion
ledger.  Each term corresponds to a literal forward/reverse segment of
`unscaledInversionGates`. -/
def unscaledInversionGateLengthBound (tail counterWidth : Nat) : Nat :=
  2 * MK.Circuit.foldGateLengthBound tail counterWidth +
    2 * Correction.correctionComputeGateLengthBound tail counterWidth +
      2 * Correction.unitMultiplicationGateLengthBound tail +
        Correction.stagedTargetAddGateLengthBound tail

/-- Width-only CNOT bound for the complete scale-removing inversion ledger,
summed from the actual forward and reverse gate-list segments. -/
def unscaledInversionCnotBound (tail counterWidth : Nat) : Nat :=
  2 * (2 * tail.succ * (4 * tail + 13)) +
    2 * Correction.correctionComputeCnotBound tail counterWidth +
      2 * Correction.unitMultiplicationCnotBound tail +
        Correction.stagedTargetAddCnotBound tail

/-- Width-only Toffoli bound for the complete scale-removing inversion
ledger, summed from the actual forward and reverse gate-list segments. -/
def unscaledInversionToffoliBound (tail counterWidth : Nat) : Nat :=
  2 * (2 * tail.succ *
    (1114 * tail + 8 * counterWidth +
      72 * (counterWidth - 1) + 801)) +
    2 * Correction.correctionComputeToffoliBound tail counterWidth +
      2 * Correction.unitMultiplicationToffoliCount tail +
        Correction.stagedTargetAddToffoliCount tail

/-- The exact scale-removing inversion gate list obeys its named width-only
primitive-leaf bound. -/
lemma unscaledInversionGates_length_le
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    (unscaledInversionGates
      tail counterWidth p comparisonIndex workIndex hpOdd).length ≤
      unscaledInversionGateLengthBound tail counterWidth := by
  have hfixed := Correction.fixedComputeGates_length_le
    tail counterWidth comparisonIndex workIndex
  have hcorrection := Correction.correctionComputeGates_length_le
    tail counterWidth p hpOdd
  have hunscale := Correction.liftedUnitMultiplicationGates_length_le
    tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)⁻¹
  have htarget := Correction.stagedTargetAddGates_length_le
    tail counterWidth p
  have hrescale := Correction.liftedUnitMultiplicationGates_length_le
    tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)
  simp only [unscaledInversionGates, unscaledInversionGateLengthBound,
    List.length_append, List.length_reverse]
  omega

/-- The exact scale-removing inversion gate list obeys its named
coordinate-specific CNOT bound. -/
lemma unscaledInversionGates_cnotMultiplicity_sum_le
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    ((unscaledInversionGates
      tail counterWidth p comparisonIndex workIndex hpOdd).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤
      unscaledInversionCnotBound tail counterWidth := by
  have hfixed := Correction.fixedComputeGates_cnotMultiplicity_sum
    tail counterWidth comparisonIndex workIndex
  have hcorrection :=
    Correction.correctionComputeGates_cnotMultiplicity_sum_le
      tail counterWidth p hpOdd
  have hunscale :=
    Correction.liftedUnitMultiplicationGates_cnotMultiplicity_sum_le
      tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)⁻¹
  have htarget := Correction.stagedTargetAddGates_cnotMultiplicity_sum_le
    tail counterWidth p
  have hrescale :=
    Correction.liftedUnitMultiplicationGates_cnotMultiplicity_sum_le
      tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)
  simp only [unscaledInversionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  unfold unscaledInversionCnotBound
  omega

/-- The exact scale-removing inversion gate list obeys its named
coordinate-specific Toffoli bound. -/
lemma unscaledInversionGates_toffoliMultiplicity_sum_le
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    ((unscaledInversionGates
      tail counterWidth p comparisonIndex workIndex hpOdd).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum ≤
      unscaledInversionToffoliBound tail counterWidth := by
  have hfixed := Correction.fixedComputeGates_toffoliMultiplicity_sum
    tail counterWidth comparisonIndex workIndex
  have hcorrection :=
    Correction.correctionComputeGates_toffoliMultiplicity_sum_le
      tail counterWidth p hpOdd
  have hunscale :=
    Correction.liftedUnitMultiplicationGates_toffoliMultiplicity_sum
      tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)⁻¹
  have htarget := Correction.stagedTargetAddGates_toffoliMultiplicity_sum
    tail counterWidth p
  have hrescale :=
    Correction.liftedUnitMultiplicationGates_toffoliMultiplicity_sum
      tail counterWidth p (montgomeryScaleUnit p tail.succ hpOdd)
  simp only [unscaledInversionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  unfold unscaledInversionToffoliBound
  omega

set_option maxHeartbeats 800000 in
-- The five-stage semantic composition unfolds a large product-register endpoint.
/-- The complete compute/correct/add/uncompute ledger restores every fixed and
VBE work register while adding the source-facing signed Montgomery residue to
the public target.  The program is static; the trace occurs only in this
post-hoc arithmetic description of the physical endpoint. -/
lemma inversionProgram_cleanEndpoint
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x))
    (target : ZMod p.val) :
    inversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
        (cleanCorrectionRegisters tail counterWidth p.val
          (MK.Circuit.withCleanRouteHistory
            tail.succ counterWidth
            (MK.initialRegisters
              tail.succ counterWidth p input))
          0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        (MK.Circuit.withCleanRouteHistory
          tail.succ counterWidth
          (MK.initialRegisters
            tail.succ counterWidth p input))
        0
        (target +
          (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
            p.val) := by
  have hnoWrap :=
    fixedRoundPaddingSteps_lt_counterCapacity tail counterWidth p.val input.val
      hinputPos hcapacity
  let _ : NeZero p.val := ⟨Nat.ne_of_gt hpOdd.pos⟩
  let initialFixed :=
    MK.Circuit.withCleanRouteHistory tail.succ counterWidth
      (MK.initialRegisters
        tail.succ counterWidth p input)
  let trace := Trace.ofInput tail.succ p.val input.val
  let signed := trace.signedCorrectedInverseResidue p.val
  change
    inversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
        (cleanCorrectionRegisters tail counterWidth p.val
          initialFixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + signed)
  have hpMod : p.val % 2 = 1 := Nat.odd_iff.mp hpOdd
  rcases fixedComputeProgram_cleanEndpoint
      tail counterWidth comparisonIndex workIndex p input hpMod hfinal arithAt
      with ⟨fixed, hcompute, hinvariant, hsource⟩
  have hcomputeBoundary (boundaryTarget : ZMod p.val) :
      fixedComputeStep tail counterWidth comparisonIndex workIndex
          (cleanCorrectionRegisters tail counterWidth p.val
            initialFixed 0 boundaryTarget) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed 0 boundaryTarget := by
    let targetWord : Word tail.succ :=
      ⟨boundaryTarget.val % 2 ^ tail.succ,
        Nat.mod_lt _ (Nat.two_pow_pos tail.succ)⟩
    simpa [cleanCorrectionRegisters, initialFixed, targetWord] using
      hcompute
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          tail.succ p.val 0 0)
        targetWord
  have hcounterRaw := hinvariant.counter_mod
  have hcounter :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val =
        (RoundState.fixedRoundState
            tail.succ p.val input.val).paddingSteps %
          2 ^ counterWidth := by
    have hcounterPrefix :
        (MK.Circuit.dataRegisters
            tail counterWidth fixed).counter.val =
          (trace.prefixState (2 * tail.succ)).paddingSteps %
            2 ^ counterWidth := by
      simpa only [trace] using hcounterRaw
    have hfull :
        trace.prefixState (2 * tail.succ) = trace.finish := by
      simpa using Trace.prefixState_full trace
    rw [hfull] at hcounterPrefix
    simpa only [trace, Trace.ofInput] using hcounterPrefix
  have hcorrection (boundaryTarget : ZMod p.val) :
      correctionComputeStep tail counterWidth p.val hpOdd
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 boundaryTarget) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed boundaryTarget := by
    simpa only [signed, trace] using
      correctionCompute_signedResidue
        tail counterWidth p.val input.val hpOdd p.isLt fixed
        hinvariant.clean hsource hcounter hnoWrap boundaryTarget
  have hadd :
      stagedTargetAddStep tail counterWidth p.val
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed signed target) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed (target + signed) := by
    exact stagedTargetAddProgram_cleanEndpoint
      tail counterWidth p.val hpOdd.pos p.isLt fixed signed target
  have huncomputeCorrection :
      EncodedBit.GateSpec.stepList
          (correctionComputeGates tail counterWidth p.val hpOdd).reverse
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed signed (target + signed)) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed 0 (target + signed) := by
    rw [← show
        EncodedBit.GateSpec.stepList
            (correctionComputeGates tail counterWidth p.val hpOdd)
            (cleanCorrectionRegisters tail counterWidth p.val
              fixed 0 (target + signed)) =
          cleanCorrectionRegisters tail counterWidth p.val
            fixed signed (target + signed) by
      simpa only [correctionComputeStep] using hcorrection (target + signed)]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (correctionComputeGates tail counterWidth p.val hpOdd)
      (cleanCorrectionRegisters tail counterWidth p.val
        fixed 0 (target + signed))
  have huncomputeFixed :
      EncodedBit.GateSpec.stepList
          (fixedComputeGates tail counterWidth comparisonIndex workIndex).reverse
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 (target + signed)) =
        cleanCorrectionRegisters tail counterWidth p.val
          initialFixed 0 (target + signed) := by
    rw [← show
        EncodedBit.GateSpec.stepList
            (fixedComputeGates tail counterWidth comparisonIndex workIndex)
            (cleanCorrectionRegisters tail counterWidth p.val
              initialFixed 0 (target + signed)) =
          cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 (target + signed) by
      simpa only [fixedComputeStep] using hcomputeBoundary (target + signed)]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (fixedComputeGates tail counterWidth comparisonIndex workIndex)
      (cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + signed))
  change EncodedBit.GateSpec.stepList
    (fixedComputeGates tail counterWidth comparisonIndex workIndex ++
      correctionComputeGates tail counterWidth p.val hpOdd ++
      stagedTargetAddGates tail counterWidth p.val ++
      (correctionComputeGates tail counterWidth p.val hpOdd).reverse ++
      (fixedComputeGates tail counterWidth comparisonIndex workIndex).reverse)
    (cleanCorrectionRegisters tail counterWidth p.val initialFixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + signed)
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [show
      EncodedBit.GateSpec.stepList
          (fixedComputeGates tail counterWidth comparisonIndex workIndex)
          (cleanCorrectionRegisters tail counterWidth p.val
            initialFixed 0 target) =
        cleanCorrectionRegisters tail counterWidth p.val fixed 0 target by
      simpa only [fixedComputeStep] using hcomputeBoundary target]
  rw [show
      EncodedBit.GateSpec.stepList
          (correctionComputeGates tail counterWidth p.val hpOdd)
          (cleanCorrectionRegisters tail counterWidth p.val fixed 0 target) =
        cleanCorrectionRegisters tail counterWidth p.val fixed signed target by
      simpa only [correctionComputeStep] using hcorrection target]
  rw [show
      EncodedBit.GateSpec.stepList
          (stagedTargetAddGates tail counterWidth p.val)
          (cleanCorrectionRegisters tail counterWidth p.val fixed signed target) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed (target + signed) by
      simpa only [stagedTargetAddStep] using hadd,
    huncomputeCorrection, huncomputeFixed]

/-- Unit-input specialization of the exact physical endpoint.  The circuit
adds the positive fixed Montgomery scale times the unit inverse; the relation
between the physical input word and the supplied unit is stated explicitly. -/
lemma inversionProgram_scaledMontgomeryEndpoint
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x))
    (u : (ZMod p.val)ˣ)
    (hinput : (input.val : ZMod p.val) = (u : ZMod p.val))
    (hfinish :
      (Trace.ofInput tail.succ p.val input.val).finish.u = 1)
    (target : ZMod p.val) :
    inversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
        (cleanCorrectionRegisters tail counterWidth p.val
          (MK.Circuit.withCleanRouteHistory
            tail.succ counterWidth
            (MK.initialRegisters
              tail.succ counterWidth p input))
          0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        (MK.Circuit.withCleanRouteHistory
          tail.succ counterWidth
          (MK.initialRegisters
            tail.succ counterWidth p input))
        0
        (target + scaledInverseResidue
          ((2 : ZMod p.val) ^ (2 * tail.succ)) u) := by
  have hmul :
      (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
            p.val *
          (u : ZMod p.val) =
        (2 : ZMod p.val) ^ (2 * tail.succ) := by
    calc
      _ =
          (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
              p.val *
            (input.val : ZMod p.val) := by
        rw [hinput]
      _ = (2 : ZMod p.val) ^ (2 * tail.succ) :=
        Trace.ofInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
          tail.succ p.val input.val hfinish
  have hsigned :
      (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
          p.val =
        scaledInverseResidue
          ((2 : ZMod p.val) ^ (2 * tail.succ)) u :=
    eq_scaledInverseResidue_of_mul_input_eq
      ((Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
        p.val)
      ((2 : ZMod p.val) ^ (2 * tail.succ)) u hmul
  simpa only [hsigned] using
    inversionProgram_cleanEndpoint tail counterWidth p input comparisonIndex
      workIndex hpOdd hinputPos hcapacity hfinal arithAt target

/-- Unit-input clean endpoint of the seven-stage static inversion ledger.
It removes the Montgomery scale before target transfer and restores the
correction workspace before reverse computation. -/
lemma unscaledInversionProgram_cleanUnitEndpoint
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x))
    (u : (ZMod p.val)ˣ)
    (hinput : (input.val : ZMod p.val) = (u : ZMod p.val))
    (hfinish :
      (Trace.ofInput tail.succ p.val input.val).finish.u = 1)
    (target : ZMod p.val) :
    unscaledInversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
        (cleanCorrectionRegisters tail counterWidth p.val
          (MK.Circuit.withCleanRouteHistory
            tail.succ counterWidth
            (MK.initialRegisters
              tail.succ counterWidth p input))
          0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        (MK.Circuit.withCleanRouteHistory
          tail.succ counterWidth
          (MK.initialRegisters
            tail.succ counterWidth p input))
        0
        (target + inverseResidue u) := by
  have hnoWrap :=
    fixedRoundPaddingSteps_lt_counterCapacity tail counterWidth p.val input.val
      hinputPos hcapacity
  let _ : NeZero p.val := ⟨Nat.ne_of_gt hpOdd.pos⟩
  let initialFixed :=
    MK.Circuit.withCleanRouteHistory tail.succ counterWidth
      (MK.initialRegisters tail.succ counterWidth p input)
  let trace := Trace.ofInput tail.succ p.val input.val
  let signed := trace.signedCorrectedInverseResidue p.val
  let unscaled : ZMod p.val :=
    unscaleResidue (inverseMontgomeryScale p.val tail.succ hpOdd) signed
  change
    unscaledInversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
        (cleanCorrectionRegisters tail counterWidth p.val
          initialFixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + inverseResidue u)
  have hmul :
      (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
            p.val *
          (u : ZMod p.val) =
        (2 : ZMod p.val) ^ (2 * tail.succ) := by
    calc
      _ =
          (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
              p.val *
            (input.val : ZMod p.val) := by
        rw [hinput]
      _ = (2 : ZMod p.val) ^ (2 * tail.succ) :=
        Trace.ofInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
          tail.succ p.val input.val hfinish
  have hsigned :
      (Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
          p.val =
        scaledInverseResidue
          ((2 : ZMod p.val) ^ (2 * tail.succ)) u :=
    eq_scaledInverseResidue_of_mul_input_eq
      ((Trace.ofInput tail.succ p.val input.val).signedCorrectedInverseResidue
        p.val)
      ((2 : ZMod p.val) ^ (2 * tail.succ)) u hmul
  have hsigned' : signed =
      scaledInverseResidue ((2 : ZMod p.val) ^ (2 * tail.succ)) u := by
    simpa only [signed, trace] using hsigned
  have hunscaled : unscaled = inverseResidue u := by
    change
      unscaleResidue (inverseMontgomeryScale p.val tail.succ hpOdd)
        signed =
      inverseResidue u
    rw [hsigned']
    exact unscaleResidue_scaledInverseResidue
      (inverseMontgomeryScale p.val tail.succ hpOdd)
      ((2 : ZMod p.val) ^ (2 * tail.succ)) u
      (inverseMontgomeryScale_mul_scale p.val tail.succ hpOdd)
  have hpMod : p.val % 2 = 1 := Nat.odd_iff.mp hpOdd
  rcases fixedComputeProgram_cleanEndpoint
      tail counterWidth comparisonIndex workIndex p input hpMod hfinal arithAt
      with ⟨fixed, hcompute, hinvariant, hsource⟩
  have hcomputeBoundary (boundaryTarget : ZMod p.val) :
      fixedComputeStep tail counterWidth comparisonIndex workIndex
          (cleanCorrectionRegisters tail counterWidth p.val
            initialFixed 0 boundaryTarget) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed 0 boundaryTarget := by
    let targetWord : Word tail.succ :=
      ⟨boundaryTarget.val % 2 ^ tail.succ,
        Nat.mod_lt _ (Nat.two_pow_pos tail.succ)⟩
    simpa [cleanCorrectionRegisters, initialFixed, targetWord] using
      hcompute
        (MAU.Multiplication.Accumulate.VBECircuit.cleanState
          tail.succ p.val 0 0)
        targetWord
  have hcounterRaw := hinvariant.counter_mod
  have hcounter :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val =
        (RoundState.fixedRoundState
            tail.succ p.val input.val).paddingSteps %
          2 ^ counterWidth := by
    have hcounterPrefix :
        (MK.Circuit.dataRegisters
            tail counterWidth fixed).counter.val =
          (trace.prefixState (2 * tail.succ)).paddingSteps %
            2 ^ counterWidth := by
      simpa only [trace] using hcounterRaw
    have hfull :
        trace.prefixState (2 * tail.succ) = trace.finish := by
      simpa using Trace.prefixState_full trace
    rw [hfull] at hcounterPrefix
    simpa only [trace, Trace.ofInput] using hcounterPrefix
  have hcorrection (boundaryTarget : ZMod p.val) :
      correctionComputeStep tail counterWidth p.val hpOdd
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 boundaryTarget) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed boundaryTarget := by
    simpa only [signed, trace] using
      correctionCompute_signedResidue
        tail counterWidth p.val input.val hpOdd p.isLt fixed
        hinvariant.clean hsource hcounter hnoWrap boundaryTarget
  have hunscale :
      liftedUnitMultiplicationStep tail counterWidth p.val
          (montgomeryScaleUnit p.val tail.succ hpOdd)⁻¹
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed signed target) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed unscaled target := by
    simpa only [unscaled, inverseMontgomeryScale, unscaleResidue] using
      liftedUnitMultiplicationProgram_cleanEndpoint
        tail counterWidth p.val hpOdd p.isLt
        (montgomeryScaleUnit p.val tail.succ hpOdd)⁻¹ fixed signed target
  have hscaleBack :
      ((montgomeryScaleUnit p.val tail.succ hpOdd : (ZMod p.val)ˣ) :
          ZMod p.val) *
        unscaled = signed := by
    change
      ((montgomeryScaleUnit p.val tail.succ hpOdd : (ZMod p.val)ˣ) :
          ZMod p.val) *
          ((((montgomeryScaleUnit p.val tail.succ hpOdd)⁻¹ :
              (ZMod p.val)ˣ) : ZMod p.val) * signed) =
        signed
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel]
    simp
  have hadd :
      stagedTargetAddStep tail counterWidth p.val
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed unscaled target) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed unscaled (target + unscaled) := by
    exact stagedTargetAddProgram_cleanEndpoint
      tail counterWidth p.val hpOdd.pos p.isLt fixed unscaled target
  have hrescale :
      liftedUnitMultiplicationStep tail counterWidth p.val
          (montgomeryScaleUnit p.val tail.succ hpOdd)
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed unscaled (target + unscaled)) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed (target + unscaled) := by
    simpa only [hscaleBack] using
      liftedUnitMultiplicationProgram_cleanEndpoint
        tail counterWidth p.val hpOdd p.isLt
        (montgomeryScaleUnit p.val tail.succ hpOdd)
        fixed unscaled (target + unscaled)
  have huncomputeCorrection :
      EncodedBit.GateSpec.stepList
          (correctionComputeGates tail counterWidth p.val hpOdd).reverse
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed signed (target + unscaled)) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed 0 (target + unscaled) := by
    rw [← show
        EncodedBit.GateSpec.stepList
            (correctionComputeGates tail counterWidth p.val hpOdd)
            (cleanCorrectionRegisters tail counterWidth p.val
              fixed 0 (target + unscaled)) =
          cleanCorrectionRegisters tail counterWidth p.val
            fixed signed (target + unscaled) by
      simpa only [correctionComputeStep] using hcorrection (target + unscaled)]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (correctionComputeGates tail counterWidth p.val hpOdd)
      (cleanCorrectionRegisters tail counterWidth p.val
        fixed 0 (target + unscaled))
  have huncomputeFixed :
      EncodedBit.GateSpec.stepList
          (fixedComputeGates tail counterWidth comparisonIndex workIndex).reverse
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 (target + unscaled)) =
        cleanCorrectionRegisters tail counterWidth p.val
          initialFixed 0 (target + unscaled) := by
    rw [← show
        EncodedBit.GateSpec.stepList
            (fixedComputeGates tail counterWidth comparisonIndex workIndex)
            (cleanCorrectionRegisters tail counterWidth p.val
              initialFixed 0 (target + unscaled)) =
          cleanCorrectionRegisters tail counterWidth p.val
            fixed 0 (target + unscaled) by
      simpa only [fixedComputeStep] using hcomputeBoundary (target + unscaled)]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (fixedComputeGates tail counterWidth comparisonIndex workIndex)
      (cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + unscaled))
  change EncodedBit.GateSpec.stepList
    (fixedComputeGates tail counterWidth comparisonIndex workIndex ++
      correctionComputeGates tail counterWidth p.val hpOdd ++
      liftedUnitMultiplicationGates tail counterWidth p.val
        (montgomeryScaleUnit p.val tail.succ hpOdd)⁻¹ ++
      stagedTargetAddGates tail counterWidth p.val ++
      liftedUnitMultiplicationGates tail counterWidth p.val
        (montgomeryScaleUnit p.val tail.succ hpOdd) ++
      (correctionComputeGates tail counterWidth p.val hpOdd).reverse ++
      (fixedComputeGates tail counterWidth comparisonIndex workIndex).reverse)
    (cleanCorrectionRegisters tail counterWidth p.val initialFixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p.val
        initialFixed 0 (target + inverseResidue u)
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [show
      EncodedBit.GateSpec.stepList
          (fixedComputeGates tail counterWidth comparisonIndex workIndex)
          (cleanCorrectionRegisters tail counterWidth p.val
            initialFixed 0 target) =
        cleanCorrectionRegisters tail counterWidth p.val fixed 0 target by
      simpa only [fixedComputeStep] using hcomputeBoundary target]
  rw [show
      EncodedBit.GateSpec.stepList
          (correctionComputeGates tail counterWidth p.val hpOdd)
          (cleanCorrectionRegisters tail counterWidth p.val fixed 0 target) =
        cleanCorrectionRegisters tail counterWidth p.val fixed signed target by
      simpa only [correctionComputeStep] using hcorrection target]
  rw [show
      EncodedBit.GateSpec.stepList
          (liftedUnitMultiplicationGates tail counterWidth p.val
            (montgomeryScaleUnit p.val tail.succ hpOdd)⁻¹)
          (cleanCorrectionRegisters tail counterWidth p.val fixed signed target) =
        cleanCorrectionRegisters tail counterWidth p.val fixed unscaled target by
      simpa only [liftedUnitMultiplicationStep] using hunscale]
  rw [show
      EncodedBit.GateSpec.stepList
          (stagedTargetAddGates tail counterWidth p.val)
          (cleanCorrectionRegisters tail counterWidth p.val fixed unscaled target) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed unscaled (target + unscaled) by
      simpa only [stagedTargetAddStep] using hadd]
  rw [show
      EncodedBit.GateSpec.stepList
          (liftedUnitMultiplicationGates tail counterWidth p.val
            (montgomeryScaleUnit p.val tail.succ hpOdd))
          (cleanCorrectionRegisters tail counterWidth p.val
            fixed unscaled (target + unscaled)) =
        cleanCorrectionRegisters tail counterWidth p.val
          fixed signed (target + unscaled) by
      simpa only [liftedUnitMultiplicationStep] using hrescale,
    huncomputeCorrection, huncomputeFixed, hunscaled]

/-- The Montgomery endpoint packages the exact scaled physical output with
the canonical, satisfiable unscale bridge to the raw unit inverse.  The second
conjunct is a semantic bridge; it does not misstate the circuit as directly
emitting an unscaled residue. -/
lemma inversionProgram_montgomeryEndpoint
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x))
    (u : (ZMod p.val)ˣ)
    (hinput : (input.val : ZMod p.val) = (u : ZMod p.val))
    (hfinish :
      (Trace.ofInput tail.succ p.val input.val).finish.u = 1)
    (target : ZMod p.val) :
    (inversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
          (cleanCorrectionRegisters tail counterWidth p.val
            (MK.Circuit.withCleanRouteHistory
              tail.succ counterWidth
              (MK.initialRegisters
                tail.succ counterWidth p input))
            0 target) =
        cleanCorrectionRegisters tail counterWidth p.val
          (MK.Circuit.withCleanRouteHistory
            tail.succ counterWidth
            (MK.initialRegisters
              tail.succ counterWidth p input))
          0
          (target + scaledInverseResidue
            ((2 : ZMod p.val) ^ (2 * tail.succ)) u)) ∧
      unscaleResidue
          (inverseMontgomeryScale p.val tail.succ hpOdd)
          (scaledInverseResidue
            ((2 : ZMod p.val) ^ (2 * tail.succ)) u) =
        inverseResidue u := by
  constructor
  · exact inversionProgram_scaledMontgomeryEndpoint
      tail counterWidth p input comparisonIndex workIndex hpOdd hinputPos
      hcapacity hfinal arithAt u hinput hfinish target
  · exact unscaleResidue_scaledInverseResidue
      (inverseMontgomeryScale p.val tail.succ hpOdd)
      ((2 : ZMod p.val) ^ (2 * tail.succ)) u
      (inverseMontgomeryScale_mul_scale p.val tail.succ hpOdd)

/-- The complete static Montgomery inversion circuit. -/
def inversionCircuit (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (Correction.encoding tail counterWidth).width).toQuantum :=
  inversionProgram tail counterWidth p comparisonIndex workIndex hpOdd

/-- Normalized clean unit-input endpoint of the same static circuit used for
resource accounting.  Input data and source-trace premises occur only in the
correctness theorem; they do not select the program or its gate list. -/
lemma inversionCircuit_applyNormalized_clean_ket
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x))
    (u : (ZMod p.val)ˣ)
    (hinput : (input.val : ZMod p.val) = (u : ZMod p.val))
    (hfinish :
      (Trace.ofInput tail.succ p.val input.val).finish.u = 1)
    (target : ZMod p.val) :
    (inversionCircuit tail counterWidth p.val comparisonIndex workIndex
        hpOdd).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
          ((Correction.encoding tail counterWidth).encode
            (cleanCorrectionRegisters tail counterWidth p.val
            (MK.Circuit.withCleanRouteHistory
              tail.succ counterWidth
              (MK.initialRegisters
                tail.succ counterWidth p input))
            0 target)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
          ((Correction.encoding tail counterWidth).encode
            (cleanCorrectionRegisters tail counterWidth p.val
            (MK.Circuit.withCleanRouteHistory
              tail.succ counterWidth
              (MK.initialRegisters
                tail.succ counterWidth p input))
            0
            (target + scaledInverseResidue
              ((2 : ZMod p.val) ^ (2 * tail.succ)) u)))) := by
  let inputData : Correction.Registers tail counterWidth :=
    cleanCorrectionRegisters tail counterWidth p.val
      (MK.Circuit.withCleanRouteHistory
        tail.succ counterWidth
        (MK.initialRegisters
          tail.succ counterWidth p input))
      0 target
  let outputData : Correction.Registers tail counterWidth :=
    cleanCorrectionRegisters tail counterWidth p.val
      (MK.Circuit.withCleanRouteHistory
        tail.succ counterWidth
        (MK.initialRegisters
          tail.succ counterWidth p input))
      0
      (target + scaledInverseResidue
        ((2 : ZMod p.val) ^ (2 * tail.succ)) u)
  have hstep :
      inversionStep tail counterWidth p.val comparisonIndex workIndex hpOdd
          inputData = outputData := by
    exact inversionProgram_scaledMontgomeryEndpoint
      tail counterWidth p input comparisonIndex workIndex hpOdd hinputPos
      hcapacity hfinal arithAt u hinput hfinish target
  change
    (inversionProgram tail counterWidth p.val comparisonIndex workIndex
      hpOdd).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
            ((Correction.encoding tail counterWidth).encode inputData))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
          ((Correction.encoding tail counterWidth).encode outputData))
  rw [(inversionProgram_realizes tail counterWidth p.val comparisonIndex
    workIndex hpOdd).apply_encoded_ket, hstep]

/-- Normalized clean endpoint with arithmetic and fixed-round termination
evidence derived from the supplied odd modulus and unit input. -/
lemma inversionCircuit_applyNormalized_clean_ket_of_unit
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p.val)
    (hinputPos : 0 < input.val)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (u : (ZMod p.val)ˣ)
    (hinput : (input.val : ZMod p.val) = (u : ZMod p.val))
    (target : ZMod p.val) :
    (inversionCircuit tail counterWidth p.val comparisonIndex workIndex
        hpOdd).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
          ((Correction.encoding tail counterWidth).encode
            (cleanCorrectionRegisters tail counterWidth p.val
            (MK.Circuit.withCleanRouteHistory
              tail.succ counterWidth
              (MK.initialRegisters
                tail.succ counterWidth p input))
            0 target)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (Correction.encoding tail counterWidth).width).basisEquiv.symm
          ((Correction.encoding tail counterWidth).encode
            (cleanCorrectionRegisters tail counterWidth p.val
            (MK.Circuit.withCleanRouteHistory
              tail.succ counterWidth
              (MK.initialRegisters
                tail.succ counterWidth p input))
            0
            (target + scaledInverseResidue
              ((2 : ZMod p.val) ^ (2 * tail.succ)) u)))) := by
  let _ : NeZero p.val := ⟨Nat.ne_of_gt hpOdd.pos⟩
  have hinputUnit : IsUnit (input.val : ZMod p.val) := by
    rw [hinput]
    exact u.isUnit
  have hinputCoprime : Nat.Coprime input.val p.val :=
    (ZMod.isUnit_iff_coprime input.val p.val).mp hinputUnit
  have hfinish :
      (Trace.ofInput tail.succ p.val input.val).finish.u = 1 := by
    change (RoundState.fixedRoundState tail.succ p.val input.val).u = 1
    exact RoundState.fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow
      tail.succ p.val input.val hpOdd.pos p.isLt input.isLt hinputCoprime.symm
  exact inversionCircuit_applyNormalized_clean_ket
    tail counterWidth p input comparisonIndex workIndex hpOdd hinputPos hcapacity
    hfinal
    (fun roundIndex x inv =>
      MK.Circuit.cleanPrefixInvariant_arithmeticCertificate
        tail counterWidth p input roundIndex.val x inv)
    u hinput hfinish target

/-- Ordered strict event trace of the complete inversion circuit. -/
def inversionEventTrace (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
      List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd).eventTrace

/-- Strict event pool of the complete inversion circuit. -/
def inversionEventCost (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd).eventCost

/-- Strict symbolic event critical path of the complete inversion circuit. -/
def inversionEventDepth (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
      DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd).eventDepth

/-- Evaluate inversion depth under literal event durations. -/
def inversionEvaluatedEventDepth (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) : Nat :=
  (inversionCircuit tail counterWidth p comparisonIndex workIndex
    hpOdd).evaluatedEventDepth assign

/-- Literal depth of one strict inversion event coordinate. -/
def inversionEventQueryDepth (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p)
    (event : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (inversionCircuit tail counterWidth p comparisonIndex workIndex
    hpOdd).eventQueryDepth event

/-- Exact multiplicity of one gate coordinate in the inversion event pool. -/
def inversionEventGateCount (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate label)
    (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd).eventCost













/-- Linearizing the complete inversion circuit's strict event depth recovers
its exact event pool. -/
lemma inversionCircuit_resourcesFromEventDepth_eq_eventCost
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    (inversionCircuit tail counterWidth p comparisonIndex workIndex
      hpOdd).resourcesFromEventDepth =
      (inversionCircuit tail counterWidth p comparisonIndex workIndex
        hpOdd).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost
    (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd)

end Resource

namespace StructuredWitness
namespace DecomposedStageWithWorkspaceWitness


/-- Linearizing this exact circuit's strict event depth recovers its event
pool. -/
lemma resourcesFromEventDepth_eq_eventCost {n counterWidth : Nat}
    (w : DecomposedStageWithWorkspaceWitness n counterWidth) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program
end DecomposedStageWithWorkspaceWitness

namespace DecomposedStageWithFullRoundWorkspaceWitness


/-- Linearizing this exact circuit's strict event depth recovers its event
pool. -/
lemma resourcesFromEventDepth_eq_eventCost {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundWorkspaceWitness n counterWidth) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program
end DecomposedStageWithFullRoundWorkspaceWitness

namespace DecomposedStageWithFullRoundPathControlWorkspaceWitness


/-- Linearizing this exact circuit's strict event depth recovers its event
pool. -/
lemma resourcesFromEventDepth_eq_eventCost {n counterWidth : Nat}
    (w : DecomposedStageWithFullRoundPathControlWorkspaceWitness
      n counterWidth) :
    w.program.resourcesFromEventDepth = w.program.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost w.program
end DecomposedStageWithFullRoundPathControlWorkspaceWitness
end StructuredWitness

end
end MK
end MAU.Inversion
end QuantumAlg

end
