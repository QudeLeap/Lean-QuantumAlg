/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Correction
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Complete compact Montgomery--Kaliski inversion

This leaf composes the direct compact fixed-round fold with the reversible
counter-driven correction.  The public target is updated in place while the
single source-history word and every borrowed work bit are uncomputed.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit
namespace CompactInversion

noncomputable section

open MK
open MK.Compact
open Nat.FixedWidth
open NumberTheory.BinaryGCD
open CompactCertificate
open CompactCorrection

/-- The terminal source state has `u = 1`; this single native X gate clears
that known bit before `u` is borrowed by the compact correction arithmetic. -/
def terminalOneClearGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  [.x ((uValueWord fieldTail.succ counterWidth).bit 0)]

/-- Circuit compiled from the one-gate terminal-`u` clearing ledger. -/
def terminalOneClearProgram (fieldTail counterWidth : Nat) :
    UnitaryCircuit (Qubits
      (MK.Compact.encoding fieldTail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (terminalOneClearGates fieldTail counterWidth)

/-- Folded action of the terminal-`u` clearing ledger. -/
def terminalOneClearStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (terminalOneClearGates fieldTail counterWidth)

/-- Clearing terminal `u = 1` changes no other compact-carrier field. -/
theorem terminalOneClearStep_state
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hu : x.core.u = 1) :
    terminalOneClearStep fieldTail counterWidth x =
      { x with core := { x.core with u := 0 } } := by
  rcases x with
    ⟨⟨u, v, compare, sCoeff, rCoeff, scratchA, scratchB, history,
      active, counter⟩, shared, target⟩
  simp only at hu
  subst u
  have hword :
      (BinaryLabelEncoding.finIdentityBit fieldTail.succ
        (WireAddress.littleEndianWire (0 : Fin fieldTail.succ))).flip
          (1 : Word fieldTail.succ) = 0 := by
    apply Fin.ext
    simp [BinaryLabelEncoding.finIdentityBit,
      BinaryLabelEncoding.ofEquivBit, WireAddress.flipBit]
  simp [terminalOneClearStep, terminalOneClearGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, uValueWord,
    liftCoreBit, rawCoreBit, RegisterBits.uValueBit, RegisterBits.uBit,
    RegisterBits.tupleUBit, BinaryLabelEncoding.prodLeftBit,
    EncodedBit.relabel, MK.registerTupleEquiv,
    MK.Compact.registerTupleEquiv, hword]

/-- The terminal-`u` clearing circuit realizes its literal native gate. -/
theorem terminalOneClear_realizes (fieldTail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ counterWidth)
      (terminalOneClearProgram fieldTail counterWidth)
      (terminalOneClearStep fieldTail counterWidth) :=
  EncodedBit.GateSpec.realizesList
    (terminalOneClearGates fieldTail counterWidth)

/-- Reverse action of the terminal-`u` clearing gate. -/
def terminalOneRestoreStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (terminalOneClearGates fieldTail counterWidth).reverse

/-- Restoring immediately after clearing terminal `u = 1` returns the whole
compact carrier, including its public target. -/
theorem terminalOneRestoreStep_after_terminalOneClearStep
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth) :
    terminalOneRestoreStep fieldTail counterWidth
        (terminalOneClearStep fieldTail counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (terminalOneClearGates fieldTail counterWidth) x

/-- Normalize the spelling of the physical counter-width fit used by the
correction loop. -/
theorem correctionWidthFit (fieldTail counterTail : Nat)
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (counterTail + 1) + 1 <= fieldTail.succ := by
  omega

set_option maxHeartbeats 800000 in
-- This bridge packages the source endpoint as the exact state expected by
-- the compact correction ledger.
/-- Clearing terminal `u = 1` converts the full compact fold endpoint into
the canonical correction boundary without changing its sole history word,
padding counter, raw coefficient, or public target. -/
theorem terminalOneClearStep_compactFold_eq_correctionBoundaryState
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (hcoprime : Nat.Coprime p.val input.val) :
    let output := compactFoldStep fieldTail counterTail hfit
      (compactInitialRegisters fieldTail counterTail p input target)
    terminalOneClearStep fieldTail (counterTail + 2) output =
      correctionBoundaryState fieldTail (counterTail + 2) output
        output.core.rCoeff p target := by
  let output := compactFoldStep fieldTail counterTail hfit
    (compactInitialRegisters fieldTail counterTail p input target)
  let fixed := RoundState.fixedRoundState fieldTail.succ p.val input.val
  have inv := compactFold_cleanPrefixInvariant fieldTail counterTail hfit
    hcounterWidth p input target hpOdd hinput
  have endpoint := compactFold_cleanEndpoint_eq_source fieldTail counterTail
    hfit hcounterWidth p input target hpOdd hinput
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) output.core
          fixed.kaliskiSteps fixed.paddingSteps = fixed := by
    simpa only [output, fixed] using endpoint.2.2
  have hpPos : 0 < p.val := by omega
  have hbudget : Nat.size p.val + Nat.size input.val <=
      2 * fieldTail.succ := by
    have hpSize : Nat.size p.val <= fieldTail.succ :=
      Nat.size_le.mpr p.isLt
    have hinputSize : Nat.size input.val <= fieldTail.succ :=
      Nat.size_le.mpr input.isLt
    omega
  have hvFixed : fixed.v = 0 := by
    exact RoundState.fixedRoundState_v_eq_zero_of_size_budget
      fieldTail.succ p.val input.val hpPos hbudget
  have huFixed : fixed.u = 1 := by
    exact RoundState.fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow
      fieldTail.succ p.val input.val hpPos p.isLt input.isLt hcoprime
  have hsFixed : fixed.sCoeff = p.val := by
    exact RoundState.fixedRoundState_sCoeff_eq_modulus_of_terminal
      fieldTail.succ p.val input.val hvFixed huFixed
  have hactiveFixed : fixed.active = false := by
    exact RoundState.fixedRoundState_active_eq_false_of_size_budget
      fieldTail.succ p.val input.val hpPos hbudget
  have huVal : output.core.u.val = fixed.u := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.u hsource
  have hvVal : output.core.v.val = fixed.v := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.v hsource
  have hsVal : output.core.sCoeff.val = fixed.sCoeff := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.sCoeff hsource
  have hactive : output.core.active = fixed.active := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.active hsource
  have hu : output.core.u = 1 := by
    apply Fin.ext
    simp [huVal, huFixed]
  have hv : output.core.v = 0 := by
    apply Fin.ext
    simp [hvVal, hvFixed]
  have hs : output.core.sCoeff = widenFixedWord fieldTail.succ p := by
    apply Fin.ext
    simpa only [widenFixedWord_val, hsFixed] using hsVal
  have hactiveFalse : output.core.active = false := by
    exact hactive.trans hactiveFixed
  have hshared :
      output.shared = cleanSharedWork fieldTail.succ (counterTail + 2) := by
    simpa only [output] using inv.shared_clean
  have hcompare : output.core.compare = false := by
    simpa only [output] using inv.compare_clean
  have hscratchA : output.core.scratchA = false := by
    simpa only [output] using inv.scratchA_clean
  have hscratchB : output.core.scratchB = false := by
    simpa only [output] using inv.scratchB_clean
  have htarget : output.target = target := by
    simpa only [output] using inv.target_eq
  have htruncateZero :
      truncateFixedWord fieldTail.succ
          (0 : Word (fieldTail.succ + 1)) = 0 := by
    apply Fin.ext
    simp [truncateFixedWord]
  change terminalOneClearStep fieldTail (counterTail + 2) output =
    correctionBoundaryState fieldTail (counterTail + 2) output
      output.core.rCoeff p target
  rw [terminalOneClearStep_state fieldTail (counterTail + 2) output hu]
  apply (MK.Compact.registerTupleEquiv fieldTail.succ
    (counterTail + 2)).injective
  simp [MK.Compact.registerTupleEquiv, correctionBoundaryState,
    doublingState, arithmeticState, hshared, hcompare, hscratchA,
    hscratchB, htarget, hv, hs, hactiveFalse, htruncateZero,
    widenFixedWord_zero, cleanSharedWork]

/-- Literal complete compact inversion ledger: compute the fixed-round
source, clear terminal `u = 1`, update the public target through reversible
correction, restore `u`, and reverse the complete source fold. -/
def compactInversionGates
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))) :=
  compactFoldGates fieldTail counterTail hfit ++
    terminalOneClearGates fieldTail (counterTail + 2) ++
    compactCorrectionGates fieldTail (counterTail + 1) p hcapacity
      (correctionWidthFit fieldTail counterTail hwidth) ++
    (terminalOneClearGates fieldTail (counterTail + 2)).reverse ++
    (compactFoldGates fieldTail counterTail hfit).reverse

/-- Circuit compiled from the literal complete compact inversion ledger. -/
def compactInversionProgram
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    UnitaryCircuit (Qubits
      (MK.Compact.encoding fieldTail.succ (counterTail + 2)).width) :=
  EncodedBit.GateSpec.programList
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth)

/-- Folded action of the complete compact inversion ledger. -/
def compactInversionStep
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth)

/-- The complete ledger executes its five named phases in physical order. -/
theorem compactInversionStep_eq_stages
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactInversionStep fieldTail counterTail p hfit hcapacity hwidth x =
      compactFoldReverseStep fieldTail counterTail hfit
        (terminalOneRestoreStep fieldTail (counterTail + 2)
          (compactCorrectionStep fieldTail (counterTail + 1) p hcapacity
            (correctionWidthFit fieldTail counterTail hwidth)
            (terminalOneClearStep fieldTail (counterTail + 2)
              (compactFoldStep fieldTail counterTail hfit x)))) := by
  simp only [compactInversionStep, compactInversionGates, compactFoldStep,
    terminalOneClearStep, compactCorrectionStep, terminalOneRestoreStep,
    compactFoldReverseStep, compactFoldReverseGates,
    EncodedBit.GateSpec.stepList_append]

set_option maxHeartbeats 1200000 in
-- The proof rewrites the physical five-stage schedule at its two clean
-- boundaries, then cancels both literal reverse gate lists.
/-- On a clean coprime input, complete compact inversion updates only the
caller-owned target.  The update is the sign-adjusted runtime-count correction
of the physical fixed-round coefficient; the input, sole history word, padding
counter, and all shared work are restored exactly. -/
theorem compactInversionStep_cleanEndpoint
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (hcoprime : Nat.Coprime p.val input.val)
    (htarget : target.val < p.val) :
    let seed := compactInitialRegisters fieldTail counterTail p input target
    let folded := compactFoldStep fieldTail counterTail hfit seed
    let hpPos : 0 < p.val := by omega
    let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
      folded.core.rCoeff
    let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
      folded.core.counter.val fieldTail.succ reduced
    let correctedLow := truncateFixedWord fieldTail.succ corrected
    let updated := modularDifferenceWord fieldTail p.val hpPos p.isLt target
      correctedLow
    compactInversionStep fieldTail counterTail p.val hfit hcapacity hwidth seed =
      compactInitialRegisters fieldTail counterTail p input updated := by
  let seed := compactInitialRegisters fieldTail counterTail p input target
  let folded := compactFoldStep fieldTail counterTail hfit seed
  let hpPos : 0 < p.val := by omega
  let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
    folded.core.rCoeff
  let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
    folded.core.counter.val fieldTail.succ reduced
  let correctedLow := truncateFixedWord fieldTail.succ corrected
  let updated := modularDifferenceWord fieldTail p.val hpPos p.isLt target
    correctedLow
  change compactInversionStep fieldTail counterTail p.val hfit hcapacity hwidth
      seed = compactInitialRegisters fieldTail counterTail p input updated
  have endpoint := compactFold_cleanEndpoint_eq_source fieldTail counterTail
    hfit hcounterWidth p input target hpOdd hinput
  have hrVal : folded.core.rCoeff.val =
      (RoundState.fixedRoundState fieldTail.succ p.val input.val).rCoeff := by
    have hsource := congrArg RoundState.rCoeff endpoint.2.2
    simpa only [seed, folded, RoundState.fromRegisters] using hsource
  have hraw : folded.core.rCoeff.val < 2 * p.val := by
    rw [hrVal]
    exact RoundState.fixedRoundState_rCoeff_lt_two_mul_modulus
      fieldTail.succ p.val input.val hpPos
  have hpOddProp : Odd p.val := Nat.odd_iff.mpr hpOdd
  have hboundary :
      terminalOneClearStep fieldTail (counterTail + 2) folded =
        correctionBoundaryState fieldTail (counterTail + 2) folded
          folded.core.rCoeff p target := by
    simpa only [seed, folded] using
      terminalOneClearStep_compactFold_eq_correctionBoundaryState
        fieldTail counterTail hfit hcounterWidth p input target hpOdd hinput
        hcoprime
  have hcorrectionRaw := compactCorrectionStep_state fieldTail
    (counterTail + 1) p.val hcapacity
    (correctionWidthFit fieldTail counterTail hwidth) folded
    folded.core.rCoeff target hpPos p.isLt hpOddProp hraw htarget
  dsimp only at hcorrectionRaw
  rw [reducedWord_eq_canonicalResidueWord] at hcorrectionRaw
  have hcorrection :
      compactCorrectionStep fieldTail (counterTail + 1) p.val hcapacity
          (correctionWidthFit fieldTail counterTail hwidth)
          (correctionBoundaryState fieldTail (counterTail + 2) folded
            folded.core.rCoeff p target) =
        correctionBoundaryState fieldTail (counterTail + 2) folded
          folded.core.rCoeff p updated := by
    simpa only [reduced, corrected, correctedLow, updated] using hcorrectionRaw
  have hfoldTarget := compactFoldStep_initial_target_frame fieldTail
    counterTail hfit p input target
  have hfoldUpdated :
      compactFoldStep fieldTail counterTail hfit
          (compactInitialRegisters fieldTail counterTail p input updated) =
        { folded with target := updated } := by
    rw [compactFoldStep_initial_target_frame fieldTail counterTail hfit p input
      updated]
    rw [show folded =
        { compactFoldStep fieldTail counterTail hfit
            (compactInitialRegisters fieldTail counterTail p input 0) with
          target := target } by
      simpa only [seed, folded] using hfoldTarget]
  have hboundaryUpdatedRaw :=
    terminalOneClearStep_compactFold_eq_correctionBoundaryState
      fieldTail counterTail hfit hcounterWidth p input updated hpOdd hinput
      hcoprime
  have hboundaryUpdated :
      terminalOneClearStep fieldTail (counterTail + 2)
          { folded with target := updated } =
        correctionBoundaryState fieldTail (counterTail + 2) folded
          folded.core.rCoeff p updated := by
    rw [hfoldUpdated] at hboundaryUpdatedRaw
    simpa only [correctionBoundaryState_update_base_target] using
      hboundaryUpdatedRaw
  rw [compactInversionStep_eq_stages, hboundary, hcorrection,
    ← hboundaryUpdated]
  rw [terminalOneRestoreStep_after_terminalOneClearStep]
  rw [← hfoldUpdated]
  exact compactFoldReverseStep_after_compactFoldStep fieldTail counterTail hfit
    (compactInitialRegisters fieldTail counterTail p input updated)

set_option maxHeartbeats 800000 in
-- The endpoint unfolds both the complete physical fold and fixed source trace.
/-- For an odd full-width modulus, the runtime-count compact correction word
is exactly the source trace's corrected Kaliski residue.  The full-width
hypothesis is what guarantees that all selected doublings fit in the physical
`n`-slot correction schedule. -/
theorem compactFold_correctedResidue_eq_trace
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (hcoprime : Nat.Coprime p.val input.val)
    (hfull : 2 ^ (fieldTail.succ - 1) <= p.val) :
    let seed := compactInitialRegisters fieldTail counterTail p input target
    let folded := compactFoldStep fieldTail counterTail hfit seed
    let hpPos : 0 < p.val := by omega
    let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
      folded.core.rCoeff
    let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
      folded.core.counter.val fieldTail.succ reduced
    (corrected.val : ZMod p.val) =
      (Trace.ofInput fieldTail.succ p.val input.val).correctedInverseResidue
        p.val := by
  let seed := compactInitialRegisters fieldTail counterTail p input target
  let folded := compactFoldStep fieldTail counterTail hfit seed
  let hpPos : 0 < p.val := by omega
  let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
    folded.core.rCoeff
  let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
    folded.core.counter.val fieldTail.succ reduced
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let fixed := RoundState.fixedRoundState fieldTail.succ p.val input.val
  change (corrected.val : ZMod p.val) = trace.correctedInverseResidue p.val
  have inv := compactFold_cleanPrefixInvariant fieldTail counterTail hfit
    hcounterWidth p input target hpOdd hinput
  have endpoint := compactFold_cleanEndpoint_eq_source fieldTail counterTail
    hfit hcounterWidth p input target hpOdd hinput
  have hrVal : folded.core.rCoeff.val = fixed.rCoeff := by
    have hsource := congrArg RoundState.rCoeff endpoint.2.2
    simpa only [seed, folded, fixed, RoundState.fromRegisters] using hsource
  have hcounter : folded.core.counter.val = fixed.paddingSteps := by
    have hcounterPrefix : folded.core.counter.val =
        (trace.prefixState (2 * fieldTail.succ)).paddingSteps := by
      simpa only [seed, folded, trace] using inv.counter_eq
    have htraceFull : trace.prefixState (2 * fieldTail.succ) = trace.finish := by
      simpa only [fixedRoundCount_eq] using Trace.prefixState_full trace
    rw [htraceFull] at hcounterPrefix
    simpa only [trace, Trace.ofInput, fixed] using hcounterPrefix
  have hpOddProp : Odd p.val := Nat.odd_iff.mpr hpOdd
  have hpadding : fixed.paddingSteps <= fieldTail.succ := by
    exact RoundState.fixedRoundState_paddingSteps_le_width_of_full_width_odd
      fieldTail.succ p.val input.val hpPos p.isLt hinput input.isLt hcoprime
      hfull hpOddProp
  have hreduced : (reduced.val : ZMod p.val) =
      (fixed.rCoeff : ZMod p.val) := by
    simp only [reduced, canonicalResidueWord_cast, hrVal]
  rw [show (corrected.val : ZMod p.val) =
      (2 : ZMod p.val) ^ min folded.core.counter.val fieldTail.succ *
        (reduced.val : ZMod p.val) by
    exact correctionResiduePrefix_cast fieldTail p.val hpPos p.isLt
      folded.core.counter.val fieldTail.succ reduced]
  rw [hcounter, Nat.min_eq_left hpadding, hreduced]
  rfl

set_option maxHeartbeats 1200000 in
-- The proof combines the physical clean endpoint with the fixed-trace
-- Montgomery identity and therefore unfolds both layers once.
/-- Clean unit-input endpoint of the literal compact ledger.  The circuit
restores the complete compact workspace and adds the Montgomery--Kaliski
residue `2^(2n) * input⁻¹` to the caller-owned target.  In particular, when
the input itself is encoded as `x * 2^n`, this is `x⁻¹ * 2^n`, exactly the
Montgomery inversion convention used by RNSL17. -/
theorem compactInversionStep_cleanMontgomeryUnitEndpoint
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (hcoprime : Nat.Coprime p.val input.val)
    (hfull : 2 ^ (fieldTail.succ - 1) <= p.val)
    (htarget : target.val < p.val)
    (u : (ZMod p.val)ˣ)
    (hinputUnit : (input.val : ZMod p.val) = (u : ZMod p.val)) :
    let seed := compactInitialRegisters fieldTail counterTail p input target
    let folded := compactFoldStep fieldTail counterTail hfit seed
    let hpPos : 0 < p.val := by omega
    let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
      folded.core.rCoeff
    let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
      folded.core.counter.val fieldTail.succ reduced
    let correctedLow := truncateFixedWord fieldTail.succ corrected
    let updated := modularDifferenceWord fieldTail p.val hpPos p.isLt target
      correctedLow
    compactInversionStep fieldTail counterTail p.val hfit hcapacity hwidth seed =
        compactInitialRegisters fieldTail counterTail p input updated ∧
      (updated.val : ZMod p.val) =
        (target.val : ZMod p.val) +
          scaledInverseResidue
            ((2 : ZMod p.val) ^ (2 * fieldTail.succ)) u := by
  let seed := compactInitialRegisters fieldTail counterTail p input target
  let folded := compactFoldStep fieldTail counterTail hfit seed
  let hpPos : 0 < p.val := by omega
  let reduced := canonicalResidueWord fieldTail p.val hpPos p.isLt
    folded.core.rCoeff
  let corrected := correctionResiduePrefix fieldTail p.val hpPos p.isLt
    folded.core.counter.val fieldTail.succ reduced
  let correctedLow := truncateFixedWord fieldTail.succ corrected
  let updated := modularDifferenceWord fieldTail p.val hpPos p.isLt target
    correctedLow
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let fixed := RoundState.fixedRoundState fieldTail.succ p.val input.val
  change
    compactInversionStep fieldTail counterTail p.val hfit hcapacity hwidth seed =
        compactInitialRegisters fieldTail counterTail p input updated ∧
      (updated.val : ZMod p.val) =
        (target.val : ZMod p.val) +
          scaledInverseResidue
            ((2 : ZMod p.val) ^ (2 * fieldTail.succ)) u
  refine ⟨?_, ?_⟩
  · simpa only [seed, folded, hpPos, reduced, corrected, correctedLow,
      updated] using
      compactInversionStep_cleanEndpoint fieldTail counterTail hfit hcapacity
        hwidth hcounterWidth p input target hpOdd hinput hcoprime htarget
  · have hcorrectedTrace : (corrected.val : ZMod p.val) =
        trace.correctedInverseResidue p.val := by
      simpa only [seed, folded, hpPos, reduced, corrected, trace] using
        compactFold_correctedResidue_eq_trace fieldTail counterTail hfit
          hcounterWidth p input target hpOdd hinput hcoprime hfull
    have hcorrectedLt : corrected.val < p.val := by
      exact correctionResiduePrefix_lt fieldTail p.val hpPos p.isLt
        folded.core.counter.val fieldTail.succ reduced (by
          simp only [reduced, canonicalResidueWord_val]
          exact Nat.mod_lt _ hpPos)
    have hcorrectedWidth : corrected.val < 2 ^ fieldTail.succ :=
      hcorrectedLt.trans p.isLt
    have hlowVal : correctedLow.val = corrected.val := by
      simp only [correctedLow, truncateFixedWord_val,
        Nat.mod_eq_of_lt hcorrectedWidth]
    have hlowLt : correctedLow.val < p.val := by
      rw [hlowVal]
      exact hcorrectedLt
    have hpPos' : 0 < p.val := hpPos
    have hfinish : trace.finish.u = 1 := by
      change fixed.u = 1
      exact RoundState.fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow
        fieldTail.succ p.val input.val hpPos' p.isLt input.isLt hcoprime
    have hmul :
        trace.signedCorrectedInverseResidue p.val * (u : ZMod p.val) =
          (2 : ZMod p.val) ^ (2 * fieldTail.succ) := by
      calc
        trace.signedCorrectedInverseResidue p.val * (u : ZMod p.val) =
            trace.signedCorrectedInverseResidue p.val *
              (input.val : ZMod p.val) := by
                rw [hinputUnit]
        _ = (2 : ZMod p.val) ^ (2 * fieldTail.succ) := by
          simpa only [trace] using
            Trace.ofInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
              fieldTail.succ p.val input.val hfinish
    have hsigned : trace.signedCorrectedInverseResidue p.val =
        scaledInverseResidue
          ((2 : ZMod p.val) ^ (2 * fieldTail.succ)) u :=
      eq_scaledInverseResidue_of_mul_input_eq
        (trace.signedCorrectedInverseResidue p.val)
        ((2 : ZMod p.val) ^ (2 * fieldTail.succ)) u hmul
    calc
      (updated.val : ZMod p.val) =
          (target.val : ZMod p.val) - (correctedLow.val : ZMod p.val) := by
        exact modularDifferenceWord_cast fieldTail p.val hpPos p.isLt target
          correctedLow hlowLt
      _ = (target.val : ZMod p.val) - (corrected.val : ZMod p.val) := by
        rw [hlowVal]
      _ = (target.val : ZMod p.val) +
          trace.signedCorrectedInverseResidue p.val := by
        rw [Trace.signedCorrectedInverseResidue_eq_neg_corrected,
          ← hcorrectedTrace]
        ring
      _ = (target.val : ZMod p.val) +
          scaledInverseResidue
            ((2 : ZMod p.val) ^ (2 * fieldTail.succ)) u := by
        rw [hsigned]

/-- The complete compact inversion circuit realizes its literal gate-list
action, so all resource claims are tied to the same native primitive ledger. -/
theorem compactInversion_realizes
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))
      (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth)
      (compactInversionStep fieldTail counterTail p hfit hcapacity hwidth) :=
  EncodedBit.GateSpec.realizesList
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth)

/-! ## Native-gate and depth ledger -/

/-- Exact X/CNOT/Toffoli/length ledger of complete compact inversion.  The
only public-constant terms are Hamming weights of gate labels that occur in
the literal source list. -/
theorem compactInversionGates_resource
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ((compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).map
        EncodedBit.GateSpec.xMultiplicity).sum =
          4 * correctionSlotOneCountSum fieldTail.succ (counterTail + 1)
              hcapacity +
            40 * fieldTail.succ * fieldTail +
            24 * fieldTail.succ * counterTail +
            152 * fieldTail.succ + 5 ∧
      ((compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
          8 * fieldTail.succ * counterTail + 126 * fieldTail.succ + 54 +
            6 * modulusOneCount fieldTail p ∧
      ((compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          448 * fieldTail.succ * fieldTail +
            230 * fieldTail.succ * fieldTail.succ +
            56 * fieldTail.succ * counterTail +
            556 * fieldTail.succ +
            4 * fieldTail.succ * modulusOneCount fieldTail p ∧
      (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).length =
          4 * correctionSlotOneCountSum fieldTail.succ (counterTail + 1)
              hcapacity +
            488 * fieldTail.succ * fieldTail +
            230 * fieldTail.succ * fieldTail.succ +
            88 * fieldTail.succ * counterTail +
            834 * fieldTail.succ +
            4 * fieldTail.succ * modulusOneCount fieldTail p +
            6 * modulusOneCount fieldTail p + 59 := by
  have hfoldX := compactFoldGates_xMultiplicity_sum fieldTail counterTail hfit
  have hfoldC := compactFoldGates_cnotMultiplicity_sum fieldTail counterTail hfit
  have hfoldT := compactFoldGates_toffoliMultiplicity_sum fieldTail counterTail hfit
  have hfoldLength := compactFoldGates_length fieldTail counterTail hfit
  rcases compactCorrectionGates_resource fieldTail (counterTail + 1) p
      hcapacity (correctionWidthFit fieldTail counterTail hwidth) with
    ⟨hcorrectionX, hcorrectionC, hcorrectionT, hcorrectionLength⟩
  simp only [compactInversionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, List.length_append,
    List.length_reverse, terminalOneClearGates, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.xMultiplicity_x,
    EncodedBit.GateSpec.cnotMultiplicity_x,
    EncodedBit.GateSpec.toffoliMultiplicity_x,
    hfoldX, hfoldC, hfoldT, hfoldLength,
    hcorrectionX, hcorrectionC, hcorrectionT, hcorrectionLength]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The event pool cardinality is exactly the length of the same literal gate
ledger used by the semantics theorem. -/
theorem compactInversionProgram_eventCost_card
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost.card =
      (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).length := by
  exact EncodedBit.GateSpec.programList_eventCost_card
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth)

/-- Direct compilation emits no opaque quantum-subroutine event. -/
theorem compactInversionProgram_quantumSubroutine_count_zero
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost = 0 := by
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth) label

/-- Exact X count of the directly compiled complete inversion. -/
theorem compactInversionProgram_x_count
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost =
      4 * correctionSlotOneCountSum fieldTail.succ (counterTail + 1)
          hcapacity +
        40 * fieldTail.succ * fieldTail +
        24 * fieldTail.succ * counterTail + 152 * fieldTail.succ + 5 := by
  rw [compactInversionProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    (compactInversionGates_resource fieldTail counterTail p hfit hcapacity
      hwidth).1]

/-- Exact CNOT count of the directly compiled complete inversion. -/
theorem compactInversionProgram_cnot_count
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost =
      8 * fieldTail.succ * counterTail + 126 * fieldTail.succ + 54 +
        6 * modulusOneCount fieldTail p := by
  rw [compactInversionProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    (compactInversionGates_resource fieldTail counterTail p hfit hcapacity
      hwidth).2.1]

/-- Exact Toffoli count of the directly compiled complete inversion. -/
theorem compactInversionProgram_toffoli_count
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost =
      448 * fieldTail.succ * fieldTail +
        230 * fieldTail.succ * fieldTail.succ +
        56 * fieldTail.succ * counterTail + 556 * fieldTail.succ +
        4 * fieldTail.succ * modulusOneCount fieldTail p := by
  rw [compactInversionProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    (compactInversionGates_resource fieldTail counterTail p hfit hcapacity
      hwidth).2.2.1]

/-- Public-constant-independent Toffoli bound for complete compact inversion. -/
theorem compactInversionGates_toffoliMultiplicity_sum_le
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ((compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum <=
      234 * fieldTail.succ * fieldTail.succ +
        448 * fieldTail.succ * fieldTail +
        56 * fieldTail.succ * counterTail + 560 * fieldTail.succ := by
  have hcorrection := compactCorrectionGates_toffoliMultiplicity_sum_le
    fieldTail (counterTail + 1) p hcapacity
      (correctionWidthFit fieldTail counterTail hwidth)
  simp only [compactInversionGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse, terminalOneClearGates,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.toffoliMultiplicity_x,
    compactFoldGates_toffoliMultiplicity_sum fieldTail counterTail hfit]
  nlinarith

/-- Public-constant-independent primitive length bound for complete compact
inversion. -/
theorem compactInversionGates_length_le
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).length <=
      234 * fieldTail.succ * fieldTail.succ +
        488 * fieldTail.succ * fieldTail +
        92 * fieldTail.succ * counterTail + 848 * fieldTail.succ + 65 := by
  have hcorrection := compactCorrectionGates_length_le fieldTail
    (counterTail + 1) p hcapacity
      (correctionWidthFit fieldTail counterTail hwidth)
  simp only [compactInversionGates, List.length_append, List.length_reverse,
    terminalOneClearGates, List.length_cons, List.length_nil,
    compactFoldGates_length fieldTail counterTail hfit]
  nlinarith

/-- The compiled Toffoli count obeys the bound derived from its literal gate
list. -/
theorem compactInversionProgram_toffoli_count_le
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventCost <=
      234 * fieldTail.succ * fieldTail.succ +
        448 * fieldTail.succ * fieldTail +
        56 * fieldTail.succ * counterTail + 560 * fieldTail.succ := by
  rw [compactInversionProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact compactInversionGates_toffoliMultiplicity_sum_le fieldTail
    counterTail p hfit hcapacity hwidth

/-- The symbolic depth is built from the same ordered primitive event trace. -/
theorem compactInversionProgram_eventDepth
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (compactInversionProgram fieldTail counterTail p hfit hcapacity hwidth).eventDepth =
      EncodedBit.GateSpec.depthOfEvents
        ((compactInversionGates fieldTail counterTail p hfit hcapacity hwidth).map
          EncodedBit.GateSpec.event) := by
  exact EncodedBit.GateSpec.programList_eventDepth
    (compactInversionGates fieldTail counterTail p hfit hcapacity hwidth)

/-- Under unit duration per native event, the strict sequential depth is
bounded by the native list-length derivation above. -/
theorem compactInversionProgram_unitDepth_le
    (fieldTail counterTail p : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (hcapacity : fieldTail.succ <= 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 <= fieldTail.succ) :
    (compactInversionProgram fieldTail counterTail p hfit hcapacity
        hwidth).evaluatedEventDepth (fun _ => 1) <=
      234 * fieldTail.succ * fieldTail.succ +
        488 * fieldTail.succ * fieldTail +
        92 * fieldTail.succ * counterTail + 848 * fieldTail.succ + 65 := by
  rw [compactInversionProgram,
    EncodedBit.GateSpec.programList_evaluatedEventDepth_unit]
  exact compactInversionGates_length_le fieldTail counterTail p hfit
    hcapacity hwidth

/-- The carrier used by the P-256 specialization has exactly 2074 qubits:
`n = 256` and the fixed-round counter width is nine. -/
theorem compactInversionCarrier_256_width :
    (MK.Compact.encoding 256 9).width = 2074 := by
  rw [MK.Compact.encoding_width_exact 256 9 (by omega)]

end
end CompactInversion
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
