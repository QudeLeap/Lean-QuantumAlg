/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold

/-!
# Compact fixed-round inversion invariant

This leaf lifts the literal compact one-round circuit contract to the full
fixed-round schedule.  It tracks only the single source history already owned
by `MK.Registers`; no second route-history family is introduced.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

open MK
open Nat.FixedWidth
open NumberTheory.BinaryGCD

namespace CompactCertificate

open MK.Compact

/-- Clean compact seed.  The source input is carried by the ordinary MK core,
the one shared workspace starts clean, and the public target is supplied by
the caller. -/
def compactInitialRegisters
    (fieldTail counterTail : Nat)
    (p input target : Word fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) where
  core := initialRegisters fieldTail.succ (counterTail + 2) p input
  shared := cleanSharedWork fieldTail.succ (counterTail + 2)
  target := target

/-- Xor-loading a classical word into a clean public target changes exactly
that target field. -/
theorem targetConstantLoadStep_zero
    (n counterWidth : Nat) (base : MK.Compact.Registers n counterWidth)
    (target : Word n) :
    EncodedBit.Word.xorConstantStep
        (targetValueWord n counterWidth) target { base with target := 0 } =
      { base with target := target } := by
  let input : MK.Compact.Registers n counterWidth :=
    { base with target := 0 }
  let output := EncodedBit.Word.xorConstantStep
    (targetValueWord n counterWidth) target input
  have hcore : output.core = input.core := by
    have hpreserve := EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (EncodedBit.Word.xorConstantGates
        (targetValueWord n counterWidth) target)
      (project := fun current : MK.Compact.Registers n counterWidth =>
        current.core)
      (by
        intro gate hgate
        rw [EncodedBit.Word.xorConstantGates] at hgate
        rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
        intro current
        exact targetValueBit_flip_core n counterWidth bit current)
      input
    simpa only [output, EncodedBit.Word.xorConstantStep] using hpreserve
  have hshared : output.shared = input.shared := by
    have hpreserve := EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (EncodedBit.Word.xorConstantGates
        (targetValueWord n counterWidth) target)
      (project := fun current : MK.Compact.Registers n counterWidth =>
        current.shared)
      (by
        intro gate hgate
        rw [EncodedBit.Word.xorConstantGates] at hgate
        rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
        intro current
        exact targetValueBit_flip_shared n counterWidth bit current)
      input
    simpa only [output, EncodedBit.Word.xorConstantStep] using hpreserve
  have htarget : output.target = target := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorConstantStep_get_target
      (targetValueWord n counterWidth) target bit
      (fun other hne => by
        simpa [targetValueWord] using
          targetValueBit_wire_ne n counterWidth hne)
      input
    rw [← targetValueBit_get n counterWidth bit output]
    change ((targetValueWord n counterWidth).bit bit).get output =
      target.val.testBit bit.val
    change ((targetValueWord n counterWidth).bit bit).get
      (EncodedBit.Word.xorConstantStep
        (targetValueWord n counterWidth) target input) =
      target.val.testBit bit.val
    rw [hread]
    rw [show ((targetValueWord n counterWidth).bit bit).get input = false by
      simp only [targetValueWord, targetValueBit_get, input]
      change Nat.testBit 0 bit.val = false
      exact Nat.zero_testBit bit.val]
    exact Bool.false_xor _
  change output = { base with target := target }
  apply (MK.Compact.registerTupleEquiv n counterWidth).injective
  simp [MK.Compact.registerTupleEquiv, hcore, hshared, htarget, input]

/-- The complete fixed-round ledger commutes with loading the caller-owned
target because no round gate reads or writes those wires. -/
theorem compactFoldStep_targetConstantLoad_comm
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (target : Word fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactFoldStep fieldTail counterTail hfit
        (EncodedBit.Word.xorConstantStep
          (targetValueWord fieldTail.succ (counterTail + 2)) target x) =
      EncodedBit.Word.xorConstantStep
        (targetValueWord fieldTail.succ (counterTail + 2)) target
        (compactFoldStep fieldTail counterTail hfit x) := by
  exact EncodedBit.Word.stepList_xorConstantStep_comm
    (compactFoldGates fieldTail counterTail hfit)
    (targetValueWord fieldTail.succ (counterTail + 2)) target
    (fun bit => by
      simpa [targetValueWord] using
        compactFoldGates_bitDisjoint_target fieldTail counterTail hfit bit)
    x

/-- The compact fixed-round ledger preserves the caller-owned target word. -/
theorem compactFoldStep_target
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    (compactFoldStep fieldTail counterTail hfit x).target = x.target := by
  apply word_eq_of_testBit_eq
  intro bit
  have hread := EncodedBit.GateSpec.stepList_get_of_bitDisjoint
    (compactFoldGates fieldTail counterTail hfit)
    (targetValueBit fieldTail.succ (counterTail + 2) bit)
    (compactFoldGates_bitDisjoint_target fieldTail counterTail hfit bit)
    x
  simpa only [compactFoldStep, targetValueBit_get] using hread

/-- Changing the caller-owned target in the clean compact seed changes only
the target field of the complete forward fold. -/
theorem compactFoldStep_initial_target_frame
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (p input target : Word fieldTail.succ) :
    compactFoldStep fieldTail counterTail hfit
        (compactInitialRegisters fieldTail counterTail p input target) =
      { compactFoldStep fieldTail counterTail hfit
          (compactInitialRegisters fieldTail counterTail p input 0) with
        target := target } := by
  let seed0 := compactInitialRegisters fieldTail counterTail p input 0
  have hload :
      EncodedBit.Word.xorConstantStep
          (targetValueWord fieldTail.succ (counterTail + 2)) target seed0 =
        compactInitialRegisters fieldTail counterTail p input target := by
    simpa only [seed0, compactInitialRegisters] using
      targetConstantLoadStep_zero fieldTail.succ (counterTail + 2) seed0 target
  rw [← hload, compactFoldStep_targetConstantLoad_comm]
  let folded := compactFoldStep fieldTail counterTail hfit seed0
  have hfoldedTarget : folded.target = 0 := by
    dsimp [folded]
    rw [compactFoldStep_target]
    rfl
  have hfoldedZero : { folded with target := 0 } = folded := by
    rw [← hfoldedTarget]
  simpa only [folded, hfoldedZero] using
    targetConstantLoadStep_zero fieldTail.succ (counterTail + 2) folded target

/-- Inductive contract for a compact prefix.  Besides the source projection,
the invariant records the exact (not modular) padding counter, one clean
shared workspace, preservation of the caller's public target, and only the
still-unwritten suffix of the sole source-history word. -/
structure CompactCleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (p input target : Word fieldTail.succ) (rounds : Nat)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) : Prop where
  rounds_le : rounds ≤ 2 * fieldTail.succ
  modulusOdd : p.val % 2 = 1
  inputPositive : 0 < input.val
  shared_clean :
    x.shared = cleanSharedWork fieldTail.succ (counterTail + 2)
  compare_clean : x.core.compare = false
  scratchA_clean : x.core.scratchA = false
  scratchB_clean : x.core.scratchB = false
  target_eq : x.target = target
  source_eq :
    let source :=
      (Trace.ofInput fieldTail.succ p.val input.val).prefixState rounds
    RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
        source.kaliskiSteps source.paddingSteps = source
  counter_eq :
    let source :=
      (Trace.ofInput fieldTail.succ p.val input.val).prefixState rounds
    x.core.counter.val = source.paddingSteps
  history_fresh :
    ∀ i : Fin (2 * fieldTail.succ), rounds ≤ i.val ->
      (historyBit fieldTail.succ (counterTail + 2) i).get x = false

/-- The clean compact seed satisfies the zero-round invariant. -/
theorem compactInitial_cleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target 0
      (compactInitialRegisters fieldTail counterTail p input target) := by
  refine
    { rounds_le := by omega
      modulusOdd := hpOdd
      inputPositive := hinput
      shared_clean := rfl
      compare_clean := rfl
      scratchA_clean := rfl
      scratchB_clean := rfl
      target_eq := rfl
      source_eq := ?_
      counter_eq := ?_
      history_fresh := ?_ }
  · simpa [Trace.prefixState, Trace.ofInput, RoundState.runRounds,
      RoundState.initial, compactInitialRegisters] using
      (RoundState.fromRegisters_initialRegisters fieldTail.succ
        (counterTail + 2) p input)
  · simp [Trace.prefixState, Trace.ofInput, RoundState.runRounds,
      RoundState.initial, compactInitialRegisters, initialRegisters]
  · intro i _
    simp [compactInitialRegisters]

/-- Every compact prefix supplies the bounded-arithmetic side conditions for
its next active Montgomery--Kaliski round. -/
theorem compactCleanPrefixInvariant_arithmeticCertificate
    (fieldTail counterTail : Nat)
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x) :
    ModeControlledSemanticStepArithmeticCertificate fieldTail
      (counterTail + 2) x.core := by
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let source := trace.prefixState rounds
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          source.kaliskiSteps source.paddingSteps = source := by
    simpa only [source, trace] using inv.source_eq
  have hpPos : 0 < p.val := by
    have hpOdd := inv.modulusOdd
    omega
  have hsourceBezout : RoundState.BezoutInvariant p.val source := by
    change RoundState.BezoutInvariant p.val
      (RoundState.runRounds rounds (RoundState.initial p.val input.val))
    exact RoundState.runRounds_bezoutInvariant rounds p.val
      (RoundState.initial p.val input.val)
      (RoundState.initial_bezoutInvariant p.val input.val)
  have hregisterBezout :
      RoundState.BezoutInvariant p.val
        (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          source.kaliskiSteps source.paddingSteps) := by
    rw [hsource]
    exact hsourceBezout
  have hbezout :
      x.core.rCoeff.val * x.core.v.val +
          x.core.sCoeff.val * x.core.u.val = p.val := by
    simpa only [RoundState.BezoutInvariant, RoundState.bezoutValue,
      RoundState.fromRegisters] using hregisterBezout
  have hsourceUPos : 0 < source.u := by
    change 0 < (RoundState.runRounds rounds
      (RoundState.initial p.val input.val)).u
    exact RoundState.runRounds_u_pos_of_pos rounds
      (RoundState.initial p.val input.val) (by
        simpa [RoundState.initial] using hpPos)
  have huPos : 0 < x.core.u.val := by
    have hsourceU : x.core.u.val = source.u := by
      simpa only [RoundState.fromRegisters] using
        congrArg RoundState.u hsource
    rw [hsourceU]
    exact hsourceUPos
  exact modeControlledSemanticStepArithmeticCertificate_of_bezout_bound
    fieldTail (counterTail + 2) p.val x.core hbezout p.isLt
    (fun _ _ => Nat.ne_of_gt huPos)

/-- The source mode/counter invariant and exact physical counter identify the
compact active flag with the zero-counter test required by the handoff. -/
theorem compactCleanPrefixInvariant_mode
    (fieldTail counterTail : Nat)
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x) :
    x.core.active = decide (x.core.counter = 0) := by
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let source := trace.prefixState rounds
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          source.kaliskiSteps source.paddingSteps = source := by
    simpa only [source, trace] using inv.source_eq
  have hactive : x.core.active = source.active := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.active hsource
  have hcounter : x.core.counter.val = source.paddingSteps := by
    simpa only [source, trace] using inv.counter_eq
  have hmode := RoundState.runRounds_activeCounterInvariant rounds
    (RoundState.initial p.val input.val)
    (RoundState.initial_activeCounterInvariant p.val input.val)
  change RoundState.activeCounterInvariant source at hmode
  rw [RoundState.activeCounterInvariant] at hmode
  rw [hactive, hmode]
  congr 1
  apply propext
  simp [Fin.ext_iff, hcounter]

/-- Under the canonical logarithmic counter width, every strict compact
prefix has room for the next handoff increment without modular wraparound. -/
theorem compactCleanPrefixInvariant_counterRoom
    (fieldTail counterTail : Nat)
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x)
    (hstrict : rounds < 2 * fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ)) :
    x.core.counter.val + 1 < 2 ^ (counterTail + 2) := by
  let source :=
    (Trace.ofInput fieldTail.succ p.val input.val).prefixState rounds
  have hcounter : x.core.counter.val = source.paddingSteps := by
    simpa only [source] using inv.counter_eq
  rw [hcounter, hcounterWidth]
  exact RoundState.runRounds_paddingSteps_succ_lt_pow_clog
    fieldTail.succ p.val input.val rounds (by omega) inv.inputPositive hstrict

/-- Stable carrier facts returned by one nonterminated active compact round.
The source arithmetic words and the current history cell intentionally remain
outside this record because they are described by the source-round theorem. -/
structure CompactActiveCarrierEndpoint
    (fieldTail counterTail : Nat)
    (historyIndex : Fin (2 * fieldTail.succ))
    (before after : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    Prop where
  shared_clean :
    after.shared = cleanSharedWork fieldTail.succ (counterTail + 2)
  compare_clean : after.core.compare = false
  scratchA_clean : after.core.scratchA = false
  scratchB_clean : after.core.scratchB = false
  target_eq : after.target = before.target
  counter_eq : after.core.counter = before.core.counter
  history_preserved :
    ∀ observedIndex : Fin (2 * fieldTail.succ),
      historyIndex ≠ observedIndex ->
      (historyBit fieldTail.succ (counterTail + 2) observedIndex).get after =
        (historyBit fieldTail.succ (counterTail + 2) observedIndex).get before

set_option maxHeartbeats 800000 in
-- The endpoint combines several bitwise preservation families for one round.
/-- One nonterminated active round restores every reusable carrier component
and preserves every stable field. -/
theorem compactRound_activeNonzero_carrierEndpoint
    (fieldTail counterTail modulus kaliskiSteps paddingSteps : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hshared :
      x.shared = cleanSharedWork fieldTail.succ (counterTail + 2))
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hactive : x.core.active = true) (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
        kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate fieldTail
      (counterTail + 2) x.core) :
    CompactActiveCarrierEndpoint fieldTail counterTail historyIndex x
      (compactRoundStep fieldTail counterTail hfit historyIndex x) := by
  have hcoeff : x.shared.coefficientAdder =
      cleanCoeffAdderWork fieldTail.succ := by
    rw [hshared]
    rfl
  have hcorrection : x.shared.correctionCounter = 0 := by
    rw [hshared]
    rfl
  have hpath : x.shared.path = false := by
    rw [hshared]
    rfl
  have hcontrol : x.shared.control = false := by
    rw [hshared]
    rfl
  have hpathBit :
      (pathBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [pathBit_get] using hpath
  have hcontrolBit :
      (controlBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [controlBit_get] using hcontrol
  have hcarry :
      (coefficientCarryInBit fieldTail.succ (counterTail + 2)).get x =
        false := by
    change x.shared.coefficientAdder.1 = false
    rw [hcoeff]
    rfl
  have hwork : ∀ bit,
      (coefficientCarryWorkBit fieldTail.succ (counterTail + 2) bit).get x =
        false := by
    intro bit
    change (BinaryLabelEncoding.finIdentityBit fieldTail.succ bit).get
      x.shared.coefficientAdder.2 = false
    rw [hcoeff]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
      fieldTail.succ bit
  have hfinal : (Fin.last fieldTail).val + 1 = fieldTail.succ := by simp
  have hvWord : x.core.v ≠ 0 := by
    intro hv
    apply hvNonzero
    simp [hv]
  have hround : compactRoundStep fieldTail counterTail hfit historyIndex x =
      activeBranchBodyStep fieldTail.succ (counterTail + 2)
        (0 : Fin fieldTail.succ) (Fin.last fieldTail)
        (0 : Fin fieldTail.succ) historyIndex x := by
    rw [compactRoundStep_eq_stages,
      compactRoundPreparedStep_eq_self_of_active_nonzero fieldTail
        counterTail hfit x hcoeff hcorrection hpath hcontrol hmode hroom
        hactive hvWord]
  have route := compactRound_activeNonzero_routeCleanup_clean fieldTail
    counterTail modulus kaliskiSteps paddingSteps hfit historyIndex x hcoeff
    hcorrection hpath hcontrol hmode hroom hactive hvNonzero hcompare
    hscratchA hscratchB hhistory hmodulusOdd hbezout arith
  have hcoeffAfter :
      (compactRoundStep fieldTail counterTail hfit historyIndex
        x).shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ := by
    rw [hround]
    exact activeBranchBody_coefficientAdder_cleanEndpoint fieldTail
      (counterTail + 2) (Fin.last fieldTail) (0 : Fin fieldTail.succ)
      historyIndex x hactive hpathBit hcontrolBit hcompare hscratchA
      hscratchB hcarry hwork hfinal
  have hcorrectionAfter :
      (compactRoundStep fieldTail counterTail hfit historyIndex
        x).shared.correctionCounter = 0 := by
    rw [hround, activeBranchBodyStep_correctionCounter fieldTail
      (counterTail + 2) (Fin.last fieldTail) (0 : Fin fieldTail.succ)
      historyIndex x hactive hpathBit hcontrolBit hcompare hscratchA
      hscratchB hcarry hwork hfinal]
    exact hcorrection
  have hcontrolAfter :
      (compactRoundStep fieldTail counterTail hfit historyIndex
        x).shared.control = false := by
    rw [← controlBit_get fieldTail.succ (counterTail + 2), hround]
    exact activeBranchBody_control_cleanEndpoint fieldTail
      (counterTail + 2) (Fin.last fieldTail) (0 : Fin fieldTail.succ)
      historyIndex x hactive hpathBit hcontrolBit hcompare hscratchA
      hscratchB hcarry hwork hfinal
  refine
    { shared_clean := ?_
      compare_clean := by
        simpa only [compareBit_get] using route.compare
      scratchA_clean := by
        simpa only [scratchABit_get] using route.scratchA
      scratchB_clean := by
        simpa only [scratchBBit_get] using route.scratchB
      target_eq := ?_
      counter_eq := ?_
      history_preserved := ?_ }
  · have hpathAfter :
        (compactRoundStep fieldTail counterTail hfit historyIndex
          x).shared.path = false := by
      simpa only [pathBit_get] using route.path
    cases hafter :
        (compactRoundStep fieldTail counterTail hfit historyIndex x).shared with
    | mk coefficientAdder correctionCounter path control =>
        have hcoeffAfter' :
            coefficientAdder = cleanCoeffAdderWork fieldTail.succ := by
          simpa only [hafter] using hcoeffAfter
        have hcorrectionAfter' : correctionCounter = 0 := by
          simpa only [hafter] using hcorrectionAfter
        have hpathAfter' : path = false := by
          simpa only [hafter] using hpathAfter
        have hcontrolAfter' : control = false := by
          simpa only [hafter] using hcontrolAfter
        simp only [cleanSharedWork]
        cases hcoeffAfter'
        cases hcorrectionAfter'
        cases hpathAfter'
        cases hcontrolAfter'
        rfl
  · rw [hround]
    exact activeBranchBodyStep_target fieldTail (counterTail + 2)
      (Fin.last fieldTail) (0 : Fin fieldTail.succ) historyIndex x hactive
      hpathBit hcontrolBit hcompare hscratchA hscratchB hcarry hwork hfinal
  · rw [hround]
    exact activeBranchBodyStep_counter fieldTail (counterTail + 2)
      (Fin.last fieldTail) (0 : Fin fieldTail.succ) historyIndex x hactive
      hpathBit hcontrolBit hcompare hscratchA hscratchB hcarry hwork hfinal
  · intro observedIndex hne
    rw [hround]
    exact activeBranchBodyStep_get_history_of_ne fieldTail
      (counterTail + 2) (Fin.last fieldTail) (0 : Fin fieldTail.succ)
      historyIndex observedIndex hne x hactive hpathBit hcontrolBit hcompare
      hscratchA hscratchB hcarry hwork hfinal

set_option maxHeartbeats 800000 in
-- The source equality and carrier endpoint are normalized together here.
/-- A nonterminated active compact round advances the clean-prefix invariant
by exactly one source round. -/
theorem compactRound_activeNonzero_cleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (hstrict : rounds < 2 * fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x)
    (hactive : x.core.active = true) (hvNonzero : x.core.v.val ≠ 0) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target
      (rounds + 1)
      (compactRoundStep fieldTail counterTail hfit
        ⟨rounds, hstrict⟩ x) := by
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let source := trace.prefixState rounds
  let roundIndex : Fin (2 * fieldTail.succ) := ⟨rounds, hstrict⟩
  let after := compactRoundStep fieldTail counterTail hfit roundIndex x
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          source.kaliskiSteps source.paddingSteps = source := by
    simpa only [source, trace] using inv.source_eq
  have hsourceActive : source.active = true := by
    have hx : x.core.active = source.active := by
      simpa only [RoundState.fromRegisters] using
        congrArg RoundState.active hsource
    rw [← hx]
    exact hactive
  have hsourceV : source.v ≠ 0 := by
    have hx : x.core.v.val = source.v := by
      simpa only [RoundState.fromRegisters] using congrArg RoundState.v hsource
    intro hv
    apply hvNonzero
    rw [hx, hv]
  have hmode := compactCleanPrefixInvariant_mode fieldTail counterTail
    p input rounds x inv
  have hroom := compactCleanPrefixInvariant_counterRoom fieldTail counterTail
    p input rounds x inv hstrict hcounterWidth
  have arith := compactCleanPrefixInvariant_arithmeticCertificate
    fieldTail counterTail p input rounds x inv
  have hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex roundIndex).val = false := by
    simpa only [historyBit_get] using
      inv.history_fresh roundIndex (by
        change rounds ≤ rounds
        omega)
  have hsourceBezout : RoundState.BezoutInvariant p.val source := by
    change RoundState.BezoutInvariant p.val
      (RoundState.runRounds rounds (RoundState.initial p.val input.val))
    exact RoundState.runRounds_bezoutInvariant rounds p.val
      (RoundState.initial p.val input.val)
      (RoundState.initial_bezoutInvariant p.val input.val)
  have hregisterBezout : RoundState.BezoutInvariant p.val
      (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
        source.kaliskiSteps source.paddingSteps) := by
    rw [hsource]
    exact hsourceBezout
  have endpoint := compactRound_activeNonzero_carrierEndpoint fieldTail
    counterTail p.val source.kaliskiSteps source.paddingSteps hfit roundIndex x
    inv.shared_clean hmode hroom hactive hvNonzero inv.compare_clean
    inv.scratchA_clean inv.scratchB_clean hhistory inv.modulusOdd
    hregisterBezout arith
  have hsourceRound := compactRound_activeNonzero_sourceRound fieldTail
    counterTail source.kaliskiSteps source.paddingSteps hfit roundIndex x
    (by rw [inv.shared_clean]; rfl) (by rw [inv.shared_clean]; rfl)
    (by rw [inv.shared_clean]; rfl) (by rw [inv.shared_clean]; rfl)
    hmode hroom hactive hvNonzero inv.compare_clean inv.scratchA_clean
    inv.scratchB_clean arith
  refine
    { rounds_le := by omega
      modulusOdd := inv.modulusOdd
      inputPositive := inv.inputPositive
      shared_clean := endpoint.shared_clean
      compare_clean := endpoint.compare_clean
      scratchA_clean := endpoint.scratchA_clean
      scratchB_clean := endpoint.scratchB_clean
      target_eq := endpoint.target_eq.trans inv.target_eq
      source_eq := ?_
      counter_eq := ?_
      history_fresh := ?_ }
  · change RoundState.fromRegisters fieldTail.succ (counterTail + 2)
        after.core (trace.prefixState (rounds + 1)).kaliskiSteps
          (trace.prefixState (rounds + 1)).paddingSteps =
        trace.prefixState (rounds + 1)
    rw [Trace.prefixState_succ]
    calc
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) after.core
          (RoundState.round source).kaliskiSteps
          (RoundState.round source).paddingSteps =
          RoundState.round
            (RoundState.fromRegisters fieldTail.succ (counterTail + 2)
              x.core source.kaliskiSteps source.paddingSteps) := by
        rw [RoundState.round_active_nonzero_kaliskiSteps source
          hsourceActive hsourceV,
          RoundState.round_active_nonzero_paddingSteps source
            hsourceActive hsourceV]
        simpa only [after, roundIndex] using hsourceRound
      _ = RoundState.round source := congrArg RoundState.round hsource
  · change after.core.counter.val =
        (trace.prefixState (rounds + 1)).paddingSteps
    rw [Trace.prefixState_succ,
      RoundState.round_active_nonzero_paddingSteps source hsourceActive
        hsourceV]
    rw [endpoint.counter_eq]
    simpa only [source, trace] using inv.counter_eq
  · intro observedIndex hfresh
    have hne : roundIndex ≠ observedIndex := by
      intro heq
      have hval := congrArg Fin.val heq
      change rounds = observedIndex.val at hval
      omega
    calc
      (historyBit fieldTail.succ (counterTail + 2) observedIndex).get after =
          (historyBit fieldTail.succ (counterTail + 2)
            observedIndex).get x := endpoint.history_preserved observedIndex hne
      _ = false := inv.history_fresh observedIndex (by omega)

set_option maxHeartbeats 800000 in
-- The exact inactive handoff record is normalized against the source round.
/-- A terminating or already inactive compact round advances the clean-prefix
invariant by one padding round. -/
theorem compactRound_inactive_cleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (hstrict : rounds < 2 * fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x)
    (hinactive : (x.core.active && !decide (x.core.v = 0)) = false) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target
      (rounds + 1)
      (compactRoundStep fieldTail counterTail hfit
        ⟨rounds, hstrict⟩ x) := by
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  let source := trace.prefixState rounds
  let roundIndex : Fin (2 * fieldTail.succ) := ⟨rounds, hstrict⟩
  let after := compactRoundStep fieldTail counterTail hfit roundIndex x
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          source.kaliskiSteps source.paddingSteps = source := by
    simpa only [source, trace] using inv.source_eq
  have hactiveEq : x.core.active = source.active := by
    simpa only [RoundState.fromRegisters] using
      congrArg RoundState.active hsource
  have hvEq : x.core.v.val = source.v := by
    simpa only [RoundState.fromRegisters] using congrArg RoundState.v hsource
  have hmode := compactCleanPrefixInvariant_mode fieldTail counterTail
    p input rounds x inv
  have hroom := compactCleanPrefixInvariant_counterRoom fieldTail counterTail
    p input rounds x inv hstrict hcounterWidth
  have hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex roundIndex).val = false := by
    simpa only [historyBit_get] using
      inv.history_fresh roundIndex (by
        change rounds ≤ rounds
        omega)
  have hstep := compactRoundStep_eq_cleanHandoff_of_inactive fieldTail
    counterTail hfit roundIndex x (by rw [inv.shared_clean]; rfl)
    (by rw [inv.shared_clean]; rfl) (by rw [inv.shared_clean]; rfl)
    (by rw [inv.shared_clean]; rfl) hmode hroom hinactive
    inv.compare_clean inv.scratchA_clean inv.scratchB_clean hhistory
  have hsourceRound := compactRound_inactive_sourceRound fieldTail counterTail
    source.kaliskiSteps source.paddingSteps hfit roundIndex x
    (by rw [inv.shared_clean]; rfl) (by rw [inv.shared_clean]; rfl)
    (by rw [inv.shared_clean]; rfl) (by rw [inv.shared_clean]; rfl)
    hmode hroom hinactive inv.compare_clean inv.scratchA_clean
    inv.scratchB_clean hhistory
  have hsourceKaliski :
      (RoundState.round source).kaliskiSteps = source.kaliskiSteps := by
    cases hxactive : x.core.active with
    | false =>
        apply RoundState.round_inactive_kaliskiSteps source
        rw [← hactiveEq]
        exact hxactive
    | true =>
        have hz : decide (x.core.v = 0) = true := by
          simpa [hxactive] using hinactive
        have hxv : x.core.v = 0 := of_decide_eq_true hz
        have hsourceActive : source.active = true := by
          rw [← hactiveEq]
          exact hxactive
        have hsourceV : source.v = 0 := by
          rw [← hvEq]
          simp [hxv]
        exact RoundState.round_active_terminated_kaliskiSteps source
          hsourceActive hsourceV
  have hsourcePadding :
      (RoundState.round source).paddingSteps = source.paddingSteps + 1 := by
    cases hxactive : x.core.active with
    | false =>
        apply RoundState.round_inactive_paddingSteps source
        rw [← hactiveEq]
        exact hxactive
    | true =>
        have hz : decide (x.core.v = 0) = true := by
          simpa [hxactive] using hinactive
        have hxv : x.core.v = 0 := of_decide_eq_true hz
        have hsourceActive : source.active = true := by
          rw [← hactiveEq]
          exact hxactive
        have hsourceV : source.v = 0 := by
          rw [← hvEq]
          simp [hxv]
        exact RoundState.round_active_terminated_paddingSteps source
          hsourceActive hsourceV
  refine
    { rounds_le := by omega
      modulusOdd := inv.modulusOdd
      inputPositive := inv.inputPositive
      shared_clean := ?_
      compare_clean := ?_
      scratchA_clean := ?_
      scratchB_clean := ?_
      target_eq := ?_
      source_eq := ?_
      counter_eq := ?_
      history_fresh := ?_ }
  · rw [hstep, inv.shared_clean]
    rfl
  · rw [hstep]
    exact inv.compare_clean
  · rw [hstep]
    exact inv.scratchA_clean
  · rw [hstep]
    exact inv.scratchB_clean
  · rw [hstep]
    exact inv.target_eq
  · change RoundState.fromRegisters fieldTail.succ (counterTail + 2)
        after.core (trace.prefixState (rounds + 1)).kaliskiSteps
          (trace.prefixState (rounds + 1)).paddingSteps =
        trace.prefixState (rounds + 1)
    rw [Trace.prefixState_succ, hsourceKaliski, hsourcePadding]
    calc
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) after.core
          source.kaliskiSteps (source.paddingSteps + 1) =
          RoundState.round
            (RoundState.fromRegisters fieldTail.succ (counterTail + 2)
              x.core source.kaliskiSteps source.paddingSteps) := by
        simpa only [after, roundIndex] using hsourceRound
      _ = RoundState.round source := congrArg RoundState.round hsource
  · change after.core.counter.val =
        (trace.prefixState (rounds + 1)).paddingSteps
    rw [Trace.prefixState_succ, hsourcePadding]
    change (compactRoundStep fieldTail counterTail hfit roundIndex
      x).core.counter.val = source.paddingSteps + 1
    rw [hstep]
    change (x.core.counter +
      inactiveCounterSourceValue counterTail.succ
        (x.core.active && !decide (x.core.v = 0))).val =
          source.paddingSteps + 1
    rw [hinactive]
    simp only [inactiveCounterSourceValue, Bool.false_eq_true, ↓reduceIte]
    have haddBound : x.core.counter.val +
        (1 : Word (counterTail + 2)).val < 2 ^ (counterTail + 2) := by
      simpa using hroom
    rw [show (x.core.counter + (1 : Word (counterTail + 2))).val =
        x.core.counter.val + 1 by
      simpa using Fin.val_add_eq_of_add_lt haddBound]
    rw [show x.core.counter.val = source.paddingSteps by
      simpa only [source, trace] using inv.counter_eq]
  · intro observedIndex hfresh
    change (historyBit fieldTail.succ (counterTail + 2)
      observedIndex).get after = false
    dsimp only [after]
    rw [hstep]
    exact inv.history_fresh observedIndex (by omega)

/-- One arbitrary compact round advances the clean prefix, with the physical
mode deciding between the active and padding lemmas above. -/
theorem compactRound_cleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input : Word fieldTail.succ) {target : Word fieldTail.succ}
    (rounds : Nat)
    (hstrict : rounds < 2 * fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (inv : CompactCleanPrefixInvariant fieldTail counterTail
      p input target rounds x) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target
      (rounds + 1)
      (compactRoundStep fieldTail counterTail hfit
        ⟨rounds, hstrict⟩ x) := by
  cases hxactive : x.core.active with
  | false =>
      exact compactRound_inactive_cleanPrefixInvariant fieldTail counterTail
        hfit hcounterWidth p input rounds hstrict x inv (by
          simp [hxactive])
  | true =>
      cases hxzero : decide (x.core.v = 0) with
      | false =>
          have hvNonzero : x.core.v.val ≠ 0 := by
            intro hv
            have hword : x.core.v = 0 := by
              apply Fin.ext
              simpa using hv
            exact (of_decide_eq_false hxzero) hword
          exact compactRound_activeNonzero_cleanPrefixInvariant fieldTail
            counterTail hfit hcounterWidth p input rounds hstrict x inv
            hxactive hvNonzero
      | true =>
          exact compactRound_inactive_cleanPrefixInvariant fieldTail
            counterTail hfit hcounterWidth p input rounds hstrict x inv (by
              simp [hxactive, hxzero])

set_option maxHeartbeats 800000 in
-- Prefix induction repeatedly composes the exact compact one-round contract.
/-- Every bounded prefix of the literal compact ledger satisfies the clean
physical/source invariant. -/
theorem compactFoldPrefix_cleanInvariant
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val)
    (rounds : Nat) (hrounds : rounds ≤ 2 * fieldTail.succ) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target rounds
      (compactFoldPrefix fieldTail counterTail hfit rounds
        (compactInitialRegisters fieldTail counterTail p input target)) := by
  induction rounds with
  | zero =>
      simpa only [compactFoldPrefix_zero] using
        compactInitial_cleanPrefixInvariant fieldTail counterTail p input target
          hpOdd hinput
  | succ rounds ih =>
      have hstrict : rounds < 2 * fieldTail.succ := by omega
      let roundIndex : Fin (2 * fieldTail.succ) := ⟨rounds, hstrict⟩
      have prefixInv := ih (by omega)
      change CompactCleanPrefixInvariant fieldTail counterTail p input target
        (rounds + 1)
        (compactFoldPrefix fieldTail counterTail hfit
          (roundIndex.val + 1)
          (compactInitialRegisters fieldTail counterTail p input target))
      rw [compactFoldPrefix_succ fieldTail counterTail hfit roundIndex]
      exact compactRound_cleanPrefixInvariant fieldTail counterTail hfit
        hcounterWidth p input rounds hstrict
        (compactFoldPrefix fieldTail counterTail hfit rounds
          (compactInitialRegisters fieldTail counterTail p input target)) prefixInv

/-- The complete literal compact fold satisfies the full-length clean-prefix
invariant. -/
theorem compactFold_cleanPrefixInvariant
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val) :
    CompactCleanPrefixInvariant fieldTail counterTail p input target
      (2 * fieldTail.succ)
      (compactFoldStep fieldTail counterTail hfit
        (compactInitialRegisters fieldTail counterTail p input target)) := by
  rw [← compactFoldPrefix_full fieldTail counterTail hfit]
  exact compactFoldPrefix_cleanInvariant fieldTail counterTail hfit
    hcounterWidth p input target hpOdd hinput (2 * fieldTail.succ) (by omega)

set_option maxHeartbeats 800000 in
-- The full trace endpoint is unfolded once after the prefix induction.
/-- The direct compact fold reaches the exact fixed-round source state while
restoring its one shared workspace and preserving the caller's public target. -/
theorem compactFold_cleanEndpoint_eq_source
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 =
      Nat.clog 2 (2 * fieldTail.succ))
    (p input target : Word fieldTail.succ)
    (hpOdd : p.val % 2 = 1) (hinput : 0 < input.val) :
    let output := compactFoldStep fieldTail counterTail hfit
      (compactInitialRegisters fieldTail counterTail p input target)
    output.shared = cleanSharedWork fieldTail.succ (counterTail + 2) ∧
      output.target = target ∧
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) output.core
          (RoundState.fixedRoundState fieldTail.succ p.val
            input.val).kaliskiSteps
          (RoundState.fixedRoundState fieldTail.succ p.val
            input.val).paddingSteps =
        RoundState.fixedRoundState fieldTail.succ p.val input.val := by
  let output := compactFoldStep fieldTail counterTail hfit
    (compactInitialRegisters fieldTail counterTail p input target)
  have inv := compactFold_cleanPrefixInvariant fieldTail counterTail hfit
    hcounterWidth p input target hpOdd hinput
  refine ⟨inv.shared_clean, inv.target_eq, ?_⟩
  let trace := Trace.ofInput fieldTail.succ p.val input.val
  have hsource :
      RoundState.fromRegisters fieldTail.succ (counterTail + 2) output.core
          (trace.prefixState (2 * fieldTail.succ)).kaliskiSteps
          (trace.prefixState (2 * fieldTail.succ)).paddingSteps =
        trace.prefixState (2 * fieldTail.succ) := by
    simpa only [output, trace] using inv.source_eq
  have hfull : trace.prefixState (2 * fieldTail.succ) = trace.finish := by
    simpa using Trace.prefixState_full trace
  rw [hfull] at hsource
  simpa only [trace, Trace.ofInput] using hsource

end CompactCertificate

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
