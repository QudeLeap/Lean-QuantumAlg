/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Fixed-round route workspace and cleanup contracts
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

open MK
open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Fixed layout and route-history bits -/

/-- Full round work together with one route bit for each of the `2n` rounds. -/
abbrev RegistersWithRouteHistory (n counterWidth : Nat) :=
  RegistersWithFullRoundPathControlWork n counterWidth × Word (2 * n)

/-- Binary encoding for the fixed round workspace and its route-history word. -/
def encoding (n counterWidth : Nat) :
    BinaryLabelEncoding (RegistersWithRouteHistory n counterWidth) :=
  BinaryLabelEncoding.prod
    (registersWithFullRoundPathControlWorkEncoding n counterWidth)
    (wordEncoding (2 * n))

/-- Add clean reusable work and a clean route-history word to one register state. -/
def withCleanRouteHistory (n counterWidth : Nat)
    (x : Registers n counterWidth) :
    RegistersWithRouteHistory n counterWidth :=
  (withCleanFullRoundPathControlWork n counterWidth x, 0)

/-- Complete basis-label carrier for the exact physical layout.  Static fold
composition lives on labels; clean endpoint theorems separately reconnect the
label action to the structured register semantics. -/
abbrev Label (n counterWidth : Nat) :=
  Fin (2 ^ (encoding n counterWidth).width)

/-- Lift a path/control-work bit over the trailing route-history word. -/
def liftPathControlBit (tail counterWidth : Nat)
    (bit : EncodedBit
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
    (wordEncoding (2 * tail.succ)) bit

/-- Lift a full-round-work bit over path, control, and route-history work. -/
def liftFullRoundBit (tail counterWidth : Nat)
    (bit : EncodedBit
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftPathControlBit tail counterWidth
    (liftFullRoundWorkBitToPathControlWork tail counterWidth bit)

/-- Lift a coefficient-state bit over every round-work field. -/
def liftCoeffStateBit (tail counterWidth : Nat)
    (bit : EncodedBit
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftFullRoundBit tail counterWidth
    (liftCoeffAdderStateBitToFullRoundWork tail counterWidth bit)

/-- Shared working path bit. -/
def workingPathBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftPathControlBit tail counterWidth
    (fullRoundPathControlWorkPathBit tail counterWidth)

/-- Shared clean work bit used by controlled gate-list decomposition. -/
def workingControlBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftPathControlBit tail counterWidth
    (fullRoundPathControlWorkControlWorkBit tail counterWidth)

/-- Active flag in the fixed route-history layout. -/
def activeBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    (coeffAdderActiveBit tail.succ counterWidth)

/-- Padding-counter carry-in bit in the fixed route-history layout. -/
def counterCarryInBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftFullRoundBit tail counterWidth
    (fullRoundWorkCounterCarryInBit tail counterWidth)

/-- Comparison result bit in the fixed route-history layout. -/
def compareBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    (coeffAdderCompareBit tail.succ counterWidth)

/-- Auxiliary branch-code bit in the fixed route-history layout. -/
def scratchABit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    (coeffAdderScratchABit tail.succ counterWidth)

/-- Stored-history branch-code bit in the fixed route-history layout. -/
def scratchBBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    (coeffAdderScratchBBit tail.succ counterWidth)

/-- Selected persistent Kaliski history bit in the fixed route-history layout. -/
def historyBit (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    (coeffAdderHistoryBit tail.succ counterWidth roundIndex)

/-- Low little-endian bit of the updated `r` coefficient. -/
def rCoeffLowBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoeffStateBit tail counterWidth
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit
      (0 : Fin (tail.succ + 1)))

/-- The route-history bit assigned to one static round index. -/
def routeHistoryBit (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
    (wordEncoding (2 * tail.succ))
    (BinaryLabelEncoding.finIdentityBit (2 * tail.succ) roundIndex)

/-! ## Physical clean-boundary contracts -/

/-- Main Kaliski registers inside the complete route-history layout. -/
def dataRegisters (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    Registers tail.succ counterWidth :=
  x.1.1.1.1.1.1

@[simp] theorem activeBit_get_dataRegisters
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (activeBit tail counterWidth).get x =
      (RegisterBits.activeBit tail.succ counterWidth).get
        (dataRegisters tail counterWidth x) := by
  rfl

@[simp] theorem compareBit_get_dataRegisters
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (compareBit tail counterWidth).get x =
      (RegisterBits.compareBit tail.succ counterWidth).get
        (dataRegisters tail counterWidth x) := by
  rfl

@[simp] theorem scratchABit_get_dataRegisters
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (scratchABit tail counterWidth).get x =
      (RegisterBits.scratchABit tail.succ counterWidth).get
        (dataRegisters tail counterWidth x) := by
  rfl

@[simp] theorem scratchBBit_get_dataRegisters
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (scratchBBit tail counterWidth).get x =
      (RegisterBits.scratchBBit tail.succ counterWidth).get
        (dataRegisters tail counterWidth x) := by
  rfl

@[simp] theorem historyBit_get_dataRegisters
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (historyBit tail counterWidth roundIndex).get x =
      (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
        (dataRegisters tail counterWidth x) := by
  rfl

@[simp] theorem rCoeffLowBit_get_dataRegisters
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (rCoeffLowBit tail counterWidth).get x =
      (RegisterBits.rCoeffValueBit tail.succ counterWidth
        (0 : Fin (tail.succ + 1))).get
        (dataRegisters tail counterWidth x) := by
  rfl

/-- Direct projection of the low `r` bit from an explicitly assembled
full-round/path/control/history state.  Keeping the full-round payload opaque
prevents endpoint proofs from unfolding the complete concrete circuit. -/
theorem rCoeffLowBit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (rCoeffLowBit tail counterWidth).get
        (((fullRound, path), control), history) =
      fullRound.1.1.1.rCoeff.val.testBit 0 := by
  change
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit
      (0 : Fin (tail.succ + 1))).get fullRound.1 =
        fullRound.1.1.1.rCoeff.val.testBit 0
  exact coeffAdderRCoeffValueWord_get_testBit tail.succ counterWidth
    (0 : Fin (tail.succ + 1)) fullRound.1

theorem activeBit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (activeBit tail counterWidth).get
        (((fullRound, path), control), history) =
      (coeffAdderActiveBit tail.succ counterWidth).get fullRound.1 := by
  rfl

theorem compareBit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (compareBit tail counterWidth).get
        (((fullRound, path), control), history) =
      (coeffAdderCompareBit tail.succ counterWidth).get fullRound.1 := by
  rfl

theorem scratchABit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (scratchABit tail counterWidth).get
        (((fullRound, path), control), history) =
      (coeffAdderScratchABit tail.succ counterWidth).get fullRound.1 := by
  rfl

theorem scratchBBit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (scratchBBit tail counterWidth).get
        (((fullRound, path), control), history) =
      (coeffAdderScratchBBit tail.succ counterWidth).get fullRound.1 := by
  rfl

theorem historyBit_get_fullRoundWork
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (historyBit tail counterWidth roundIndex).get
        (((fullRound, path), control), history) =
      (coeffAdderHistoryBit tail.succ counterWidth roundIndex).get
        fullRound.1 := by
  rfl

theorem counterCarryInBit_get_fullRoundWork
    (tail counterWidth : Nat)
    (fullRound : RegistersWithFullRoundWork tail.succ counterWidth)
    (path control : Bool) (history : Word (2 * tail.succ)) :
    (counterCarryInBit tail counterWidth).get
        (((fullRound, path), control), history) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).get fullRound := by
  rfl

@[simp] theorem counterCarryInBit_get_counterWork
    (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (counterCarryInBit tail counterWidth).get x =
      (counterIncrementCarryInBit counterWidth).get x.1.1.1.2 := by
  rfl

/-- Exact reusable-work boundary.  The equality covers the complete
comparison, coefficient-adder, counter-increment, path, and control workspace;
register scratch fields remain explicit below because they are part of the
main register object rather than this appended work. -/
structure PhysicalWorkspaceClean (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop where
  workspace :
    x.1 = withCleanFullRoundPathControlWork tail.succ counterWidth
      (dataRegisters tail counterWidth x)
  scratchA : (dataRegisters tail counterWidth x).scratchA = false
  scratchB : (dataRegisters tail counterWidth x).scratchB = false
  compare : (dataRegisters tail counterWidth x).compare = false

/-- Inputs required at one static round boundary.  Only the current persistent
history and route slots must be fresh; earlier slots may already contain the
prefix history. -/
structure RoundCleanInput (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop
    extends PhysicalWorkspaceClean tail counterWidth x where
  historyFresh :
    (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
      (dataRegisters tail counterWidth x) = false
  routeFresh : (routeHistoryBit tail counterWidth roundIndex).get x = false

/-- Reusable ancillas that must already be clean before branch-residue
cleanup.  The working path and the four residue targets are intentionally not
constrained here: cleanup clears the targets, while the spill/reset suffix
clears the path. -/
structure ReusableWorkspaceClean (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop where
  comparisonWork :
    x.1.1.1.1.1.2 = cleanComparisonWork tail.succ
  coefficientWork :
    x.1.1.1.1.2 = cleanCoeffAdderWork tail.succ
  counterSource : x.1.1.1.2.1 = 1
  counterCarryWork :
    x.1.1.1.2.2.2 =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth
  control : x.1.2 = false

/-- Physical and source-semantic endpoint of one fixed round. -/
structure RoundCleanBoundary (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) (source : RoundState)
    (before after : RegistersWithRouteHistory tail.succ counterWidth) : Prop
    extends PhysicalWorkspaceClean tail counterWidth after where
  sourceAfter :
    RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth after)
        (RoundState.round source).kaliskiSteps
        (RoundState.round source).paddingSteps =
      RoundState.round source
  counterAfter :
    (dataRegisters tail counterWidth after).counter.val =
      (RoundState.round source).paddingSteps % 2 ^ counterWidth
  historyWritten :
    (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
        (dataRegisters tail counterWidth after) =
      RoundState.historyBit source
  routeWritten :
    (routeHistoryBit tail counterWidth roundIndex).get after = source.active
  historyPreserved :
    ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
      (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth after) =
        (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth before)
  routePreserved :
    ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
      (routeHistoryBit tail counterWidth observed).get after =
        (routeHistoryBit tail counterWidth observed).get before

/-- Source data, padding counter, and branch-history facts at the routed
endpoint immediately before common physical residue cleanup.  Route history
is intentionally absent: the routed prefix does not touch it, and the common
spill/reset suffix handles the current route slot uniformly. -/
structure RoutedPersistentBoundary (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) (source : RoundState)
    (before routed : RegistersWithRouteHistory tail.succ counterWidth) : Prop
    where
  sourceAfter :
    RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth routed)
        (RoundState.round source).kaliskiSteps
        (RoundState.round source).paddingSteps =
      RoundState.round source
  counterAfter :
    (dataRegisters tail counterWidth routed).counter.val =
      (RoundState.round source).paddingSteps % 2 ^ counterWidth
  historyWritten :
    (RegisterBits.historyBit tail.succ counterWidth roundIndex).get
        (dataRegisters tail counterWidth routed) =
      RoundState.historyBit source
  historyPreserved :
    ∀ observed : Fin (2 * tail.succ), roundIndex ≠ observed ->
      (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth routed) =
        (RegisterBits.historyBit tail.succ counterWidth observed).get
          (dataRegisters tail counterWidth before)

theorem prodLeftBit_prodRightBit_wire_ne
    {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right)
    (leftBit : EncodedBit left) (rightBit : EncodedBit right) :
    (BinaryLabelEncoding.prodLeftBit left right leftBit).wire ≠
      (BinaryLabelEncoding.prodRightBit left right rightBit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have hlt : leftBit.wire.val < left.width := leftBit.wire.isLt
  simp [BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

private theorem liftFullRoundBit_wire_ne
    (tail counterWidth : Nat)
    {left right : EncodedBit
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)}
    (h : left.wire ≠ right.wire) :
    (liftFullRoundBit tail counterWidth left).wire ≠
      (liftFullRoundBit tail counterWidth right).wire := by
  exact EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding (2 * tail.succ))
    (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool h))

private theorem liftCoeffStateBit_wire_ne
    (tail counterWidth : Nat)
    {left right : EncodedBit
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)}
    (h : left.wire ≠ right.wire) :
    (liftCoeffStateBit tail counterWidth left).wire ≠
      (liftCoeffStateBit tail counterWidth right).wire := by
  exact liftFullRoundBit_wire_ne tail counterWidth
    (EncodedBit.GateSpec.prodLeftWire_ne
      (counterIncrementWorkEncoding counterWidth) h)

private theorem liftRegisterBit_wire_ne
    (tail counterWidth : Nat)
    {left right : EncodedBit (registerEncoding tail.succ counterWidth)}
    (h : left.wire ≠ right.wire) :
    (liftCoeffStateBit tail counterWidth
        (liftComparisonStateBitToCoeffAdderWork tail.succ counterWidth
          (liftRegisterBitToComparisonWork tail.succ counterWidth left))).wire ≠
      (liftCoeffStateBit tail counterWidth
        (liftComparisonStateBitToCoeffAdderWork tail.succ counterWidth
          (liftRegisterBitToComparisonWork tail.succ counterWidth right))).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (EncodedBit.GateSpec.prodLeftWire_ne (coeffAdderWorkEncoding tail.succ)
      (EncodedBit.GateSpec.prodLeftWire_ne (comparisonWorkEncoding tail.succ) h))

theorem activeBit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) :
    (activeBit tail counterWidth).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    (coeffAdderActiveBit tail.succ counterWidth)
    (counterIncrementCarryInBit counterWidth)

theorem scratchABit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) :
    (scratchABit tail counterWidth).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (counterIncrementCarryInBit counterWidth)

theorem scratchBBit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) :
    (scratchBBit tail counterWidth).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (counterIncrementCarryInBit counterWidth)

theorem compareBit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) :
    (compareBit tail counterWidth).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (counterIncrementCarryInBit counterWidth)

theorem historyBit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (historyBit tail counterWidth roundIndex).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    (coeffAdderHistoryBit tail.succ counterWidth roundIndex)
    (counterIncrementCarryInBit counterWidth)

theorem rCoeffLowBit_counterCarryInBit_wire_ne
    (tail counterWidth : Nat) :
    (rCoeffLowBit tail counterWidth).wire ≠
      (counterCarryInBit tail counterWidth).wire := by
  apply liftFullRoundBit_wire_ne
  exact prodLeftBit_prodRightBit_wire_ne
    (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
    (counterIncrementWorkEncoding counterWidth)
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit
      (0 : Fin (tail.succ + 1)))
    (counterIncrementCarryInBit counterWidth)

theorem scratchABit_scratchBBit_wire_ne (tail counterWidth : Nat) :
    (scratchABit tail counterWidth).wire ≠
      (scratchBBit tail counterWidth).wire := by
  simpa [scratchABit, scratchBBit, coeffAdderScratchABit,
    coeffAdderScratchBBit, liftedScratchABit, liftedScratchBBit] using
    liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.scratchA_scratchB_wire_ne tail.succ counterWidth)

theorem scratchABit_compareBit_wire_ne (tail counterWidth : Nat) :
    (scratchABit tail counterWidth).wire ≠
      (compareBit tail counterWidth).wire := by
  simpa [scratchABit, compareBit, coeffAdderScratchABit,
    coeffAdderCompareBit, liftedScratchABit, liftedCompareBit] using
    (liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.compare_scratchA_wire_ne tail.succ counterWidth).symm)

theorem scratchBBit_compareBit_wire_ne (tail counterWidth : Nat) :
    (scratchBBit tail counterWidth).wire ≠
      (compareBit tail counterWidth).wire := by
  simpa [scratchBBit, compareBit, coeffAdderScratchBBit,
    coeffAdderCompareBit, liftedScratchBBit, liftedCompareBit] using
    (liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.compare_scratchB_wire_ne tail.succ counterWidth).symm)

theorem historyBit_scratchBBit_wire_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (historyBit tail counterWidth roundIndex).wire ≠
      (scratchBBit tail counterWidth).wire := by
  simpa [historyBit, scratchBBit, coeffAdderHistoryBit,
    coeffAdderScratchBBit, liftedHistoryBit, liftedScratchBBit] using
    (liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.scratchB_history_wire_ne
        tail.succ counterWidth roundIndex).symm)

theorem scratchABit_historyBit_wire_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (scratchABit tail counterWidth).wire ≠
      (historyBit tail counterWidth roundIndex).wire := by
  simpa [scratchABit, historyBit, coeffAdderScratchABit,
    coeffAdderHistoryBit, liftedScratchABit, liftedHistoryBit] using
    liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.scratchA_history_wire_ne
        tail.succ counterWidth roundIndex)

theorem compareBit_historyBit_wire_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (compareBit tail counterWidth).wire ≠
      (historyBit tail counterWidth roundIndex).wire := by
  simpa [compareBit, historyBit, coeffAdderCompareBit,
    coeffAdderHistoryBit, liftedCompareBit, liftedHistoryBit] using
    liftRegisterBit_wire_ne tail counterWidth
      (RegisterBits.compare_history_wire_ne
        tail.succ counterWidth roundIndex)

theorem activeBit_compareBit_wire_ne (tail counterWidth : Nat) :
    (activeBit tail counterWidth).wire ≠
      (compareBit tail counterWidth).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderActiveBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth)

theorem activeBit_scratchBBit_wire_ne (tail counterWidth : Nat) :
    (activeBit tail counterWidth).wire ≠
      (scratchBBit tail counterWidth).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)

theorem compareBit_rCoeffLowBit_wire_ne (tail counterWidth : Nat) :
    (compareBit tail counterWidth).wire ≠
      (rCoeffLowBit tail counterWidth).wire := by
  apply liftCoeffStateBit_wire_ne
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
    tail.succ counterWidth
    (liftedCompareBit tail.succ counterWidth)
    ((liftedRCoeffValueWord tail.succ counterWidth).bit
      (0 : Fin (tail.succ + 1)))
    (liftedCompare_liftedRCoeffValueWordBit_wire_ne
      tail.succ counterWidth (0 : Fin (tail.succ + 1)))

theorem rCoeffLowBit_scratchBBit_wire_ne (tail counterWidth : Nat) :
    (rCoeffLowBit tail counterWidth).wire ≠
      (scratchBBit tail counterWidth).wire := by
  apply liftCoeffStateBit_wire_ne
  exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
    tail.succ counterWidth
    ((liftedRCoeffValueWord tail.succ counterWidth).bit
      (0 : Fin (tail.succ + 1)))
    (liftedScratchBBit tail.succ counterWidth)
    (by
      exact liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.rCoeffValueBit tail.succ counterWidth
          (0 : Fin (tail.succ + 1)))
        (RegisterBits.scratchBBit tail.succ counterWidth)
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            RegisterBits.rCoeff_scratchB_wire_ne
              tail.succ counterWidth
              (WireAddress.littleEndianWire
                (0 : Fin (tail.succ + 1)))))

theorem activeBit_rCoeffLowBit_wire_ne (tail counterWidth : Nat) :
    (activeBit tail counterWidth).wire ≠
      (rCoeffLowBit tail counterWidth).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne
      tail.succ counterWidth (0 : Fin (tail.succ + 1)))

theorem activeBit_scratchABit_wire_ne (tail counterWidth : Nat) :
    (activeBit tail counterWidth).wire ≠
      (scratchABit tail counterWidth).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth)

theorem rCoeffLowBit_scratchABit_wire_ne (tail counterWidth : Nat) :
    (rCoeffLowBit tail counterWidth).wire ≠
      (scratchABit tail counterWidth).wire := by
  exact liftCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne
      tail.succ counterWidth (0 : Fin (tail.succ + 1))).symm

/-! ## Physical branch-residue cleanup -/

/-- Six-gate source-shaped cleanup of branch code, compare, and odd-branch
counter carry.  The final Toffoli is current-active controlled so terminated
and padding rounds cannot dirty `scratchA` from an unrelated coefficient bit. -/
def branchResidueCleanupGates (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  [ EncodedBit.GateSpec.cnot
      (activeBit tail counterWidth)
      (counterCarryInBit tail counterWidth)
      (activeBit_counterCarryInBit_wire_ne tail counterWidth)
  , EncodedBit.GateSpec.cnot
      (scratchABit tail counterWidth)
      (counterCarryInBit tail counterWidth)
      (scratchABit_counterCarryInBit_wire_ne tail counterWidth)
  , EncodedBit.GateSpec.cnot
      (scratchBBit tail counterWidth)
      (counterCarryInBit tail counterWidth)
      (scratchBBit_counterCarryInBit_wire_ne tail counterWidth)
  , EncodedBit.GateSpec.toffoli
      (scratchABit tail counterWidth)
      (scratchBBit tail counterWidth)
      (compareBit tail counterWidth)
      (scratchABit_scratchBBit_wire_ne tail counterWidth)
      (scratchABit_compareBit_wire_ne tail counterWidth)
      (scratchBBit_compareBit_wire_ne tail counterWidth)
  , EncodedBit.GateSpec.cnot
      (historyBit tail counterWidth roundIndex)
      (scratchBBit tail counterWidth)
      (historyBit_scratchBBit_wire_ne tail counterWidth roundIndex)
  , EncodedBit.GateSpec.toffoli
      (activeBit tail counterWidth)
      (rCoeffLowBit tail counterWidth)
      (scratchABit tail counterWidth)
      (activeBit_rCoeffLowBit_wire_ne tail counterWidth)
      (activeBit_scratchABit_wire_ne tail counterWidth)
      (rCoeffLowBit_scratchABit_wire_ne tail counterWidth) ]

/-- Semantic action of the branch-residue cleanup gate list. -/
def branchResidueCleanupStep (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (branchResidueCleanupGates tail counterWidth roundIndex)

/-- Base-gate program implementing branch-residue cleanup. -/
def branchResidueCleanupProgram (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (branchResidueCleanupGates tail counterWidth roundIndex)

theorem branchResidueCleanup_realizes (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (branchResidueCleanupProgram tail counterWidth roundIndex)
      (branchResidueCleanupStep tail counterWidth roundIndex) :=
  EncodedBit.GateSpec.realizesList
    (branchResidueCleanupGates tail counterWidth roundIndex)

/-- The four Boolean identities that characterize the garbage left by one
active-only route and are sufficient for the six cleanup gates. -/
structure BranchResidueCertificate (tail counterWidth : Nat)
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop where
  counterCarry :
    (counterCarryInBit tail counterWidth).get x =
      ((activeBit tail counterWidth).get x ^^
        (scratchABit tail counterWidth).get x ^^
        (scratchBBit tail counterWidth).get x)
  compare :
    (compareBit tail counterWidth).get x =
      ((scratchABit tail counterWidth).get x &&
        (scratchBBit tail counterWidth).get x)
  history :
    (scratchBBit tail counterWidth).get x =
      (historyBit tail counterWidth roundIndex).get x
  auxiliary :
    (scratchABit tail counterWidth).get x =
      ((activeBit tail counterWidth).get x &&
        (rCoeffLowBit tail counterWidth).get x)

/-- Degenerate certificate shared by inactive and terminating paths.  When
active and all named residue bits are false, coefficient parity is irrelevant
because the final auxiliary cleanup Toffoli is inactive. -/
theorem branchResidueCertificate_of_all_false
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hactive : (activeBit tail counterWidth).get x = false)
    (hcounter : (counterCarryInBit tail counterWidth).get x = false)
    (hcompare : (compareBit tail counterWidth).get x = false)
    (hscratchA : (scratchABit tail counterWidth).get x = false)
    (hscratchB : (scratchBBit tail counterWidth).get x = false)
    (hhistory : (historyBit tail counterWidth roundIndex).get x = false) :
    BranchResidueCertificate tail counterWidth roundIndex x := by
  refine
    { counterCarry := ?_
      compare := ?_
      history := ?_
      auxiliary := ?_ }
  · rw [hcounter, hactive, hscratchA, hscratchB]
    rfl
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive]
    rfl

/-- Residue truth table for the active `uEven` route. -/
theorem branchResidueCertificate_uEven
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hactive : (activeBit tail counterWidth).get x = true)
    (hcounter : (counterCarryInBit tail counterWidth).get x = false)
    (hcompare : (compareBit tail counterWidth).get x = false)
    (hscratchA : (scratchABit tail counterWidth).get x = true)
    (hscratchB : (scratchBBit tail counterWidth).get x = false)
    (hhistory : (historyBit tail counterWidth roundIndex).get x = false)
    (hrLow : (rCoeffLowBit tail counterWidth).get x = true) :
    BranchResidueCertificate tail counterWidth roundIndex x := by
  refine
    { counterCarry := ?_
      compare := ?_
      history := ?_
      auxiliary := ?_ }
  · rw [hcounter, hactive, hscratchA, hscratchB]
    rfl
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

/-- Residue truth table for the active `vEven` route. -/
theorem branchResidueCertificate_vEven
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hactive : (activeBit tail counterWidth).get x = true)
    (hcounter : (counterCarryInBit tail counterWidth).get x = false)
    (hcompare : (compareBit tail counterWidth).get x = false)
    (hscratchA : (scratchABit tail counterWidth).get x = false)
    (hscratchB : (scratchBBit tail counterWidth).get x = true)
    (hhistory : (historyBit tail counterWidth roundIndex).get x = true)
    (hrLow : (rCoeffLowBit tail counterWidth).get x = false) :
    BranchResidueCertificate tail counterWidth roundIndex x := by
  refine
    { counterCarry := ?_
      compare := ?_
      history := ?_
      auxiliary := ?_ }
  · rw [hcounter, hactive, hscratchA, hscratchB]
    rfl
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

/-- Residue truth table for the active odd `uGreater` route. -/
theorem branchResidueCertificate_uGreater
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hactive : (activeBit tail counterWidth).get x = true)
    (hcounter : (counterCarryInBit tail counterWidth).get x = true)
    (hcompare : (compareBit tail counterWidth).get x = true)
    (hscratchA : (scratchABit tail counterWidth).get x = true)
    (hscratchB : (scratchBBit tail counterWidth).get x = true)
    (hhistory : (historyBit tail counterWidth roundIndex).get x = true)
    (hrLow : (rCoeffLowBit tail counterWidth).get x = true) :
    BranchResidueCertificate tail counterWidth roundIndex x := by
  refine
    { counterCarry := ?_
      compare := ?_
      history := ?_
      auxiliary := ?_ }
  · rw [hcounter, hactive, hscratchA, hscratchB]
    rfl
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

/-- Residue truth table for the active odd `vLe` route. -/
theorem branchResidueCertificate_vLe
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hactive : (activeBit tail counterWidth).get x = true)
    (hcounter : (counterCarryInBit tail counterWidth).get x = true)
    (hcompare : (compareBit tail counterWidth).get x = false)
    (hscratchA : (scratchABit tail counterWidth).get x = false)
    (hscratchB : (scratchBBit tail counterWidth).get x = false)
    (hhistory : (historyBit tail counterWidth roundIndex).get x = false)
    (hrLow : (rCoeffLowBit tail counterWidth).get x = false) :
    BranchResidueCertificate tail counterWidth roundIndex x := by
  refine
    { counterCarry := ?_
      compare := ?_
      history := ?_
      auxiliary := ?_ }
  · rw [hcounter, hactive, hscratchA, hscratchB]
    rfl
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

/-- Carried branch-code staging changes only the two scratch-code targets, so
the physical compare bit is preserved. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  change (liftedCompareBit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x.1) =
      (liftedCompareBit n counterWidth).get x.1
  change (RegisterBits.compareBit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x.1.1) =
      (RegisterBits.compareBit n counterWidth).get x.1.1
  exact activeBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth branch (RegisterBits.compareBit n counterWidth)
    (Ne.symm (RegisterBits.compare_scratchA_wire_ne n counterWidth))
    (Ne.symm (RegisterBits.compare_scratchB_wire_ne n counterWidth)) x.1.1

/-- The complete carried branch-code/history/aux-shift suffix preserves the
physical compare bit. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex branch x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_compare]
  exact coeffWorkActiveBranchCodeToScratchStep_get_compare
    n counterWidth branch x

/-- Exact carry-bit effect of the first three cleanup CNOTs. -/
theorem branchResidueCleanupStep_get_counterCarry
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (counterCarryInBit tail counterWidth).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      ((((counterCarryInBit tail counterWidth).get x ^^
        (activeBit tail counterWidth).get x) ^^
        (scratchABit tail counterWidth).get x) ^^
        (scratchBBit tail counterWidth).get x) := by
  let a := activeBit tail counterWidth
  let c := counterCarryInBit tail counterWidth
  let cmp := compareBit tail counterWidth
  let sa := scratchABit tail counterWidth
  let sb := scratchBBit tail counterWidth
  let h := historyBit tail counterWidth roundIndex
  let r := rCoeffLowBit tail counterWidth
  let pre := EncodedBit.cnotStep sb c
    (EncodedBit.cnotStep sa c (EncodedBit.cnotStep a c x))
  change c.get (EncodedBit.toffoliStep a r sa
    (EncodedBit.cnotStep h sb
      (EncodedBit.toffoliStep sa sb cmp pre))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne a r sa c
    (scratchABit_counterCarryInBit_wire_ne tail counterWidth)]
  rw [EncodedBit.cnotStep_get_of_target_ne h sb c
    (scratchBBit_counterCarryInBit_wire_ne tail counterWidth)]
  rw [EncodedBit.toffoliStep_get_of_target_ne sa sb cmp c
    (compareBit_counterCarryInBit_wire_ne tail counterWidth)]
  simp only [pre]
  rw [EncodedBit.cnotStep_get_target sb c,
    EncodedBit.cnotStep_get_target sa c,
    EncodedBit.cnotStep_get_of_target_ne sa c sb
      (scratchBBit_counterCarryInBit_wire_ne tail counterWidth).symm,
    EncodedBit.cnotStep_get_target a c,
    EncodedBit.cnotStep_get_of_target_ne a c sa
      (scratchABit_counterCarryInBit_wire_ne tail counterWidth).symm,
    EncodedBit.cnotStep_get_of_target_ne a c sb
      (scratchBBit_counterCarryInBit_wire_ne tail counterWidth).symm]

/-- Exact compare-bit effect of the fourth cleanup gate. -/
theorem branchResidueCleanupStep_get_compare
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (compareBit tail counterWidth).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      ((compareBit tail counterWidth).get x ^^
        ((scratchABit tail counterWidth).get x &&
          (scratchBBit tail counterWidth).get x)) := by
  let a := activeBit tail counterWidth
  let c := counterCarryInBit tail counterWidth
  let cmp := compareBit tail counterWidth
  let sa := scratchABit tail counterWidth
  let sb := scratchBBit tail counterWidth
  let h := historyBit tail counterWidth roundIndex
  let r := rCoeffLowBit tail counterWidth
  let pre := EncodedBit.cnotStep sb c
    (EncodedBit.cnotStep sa c (EncodedBit.cnotStep a c x))
  have hpre (observed : EncodedBit (encoding tail.succ counterWidth))
      (hne : c.wire ≠ observed.wire) :
      observed.get pre = observed.get x := by
    simp only [pre]
    rw [EncodedBit.cnotStep_get_of_target_ne sb c observed hne,
      EncodedBit.cnotStep_get_of_target_ne sa c observed hne,
      EncodedBit.cnotStep_get_of_target_ne a c observed hne]
  change cmp.get (EncodedBit.toffoliStep a r sa
    (EncodedBit.cnotStep h sb
      (EncodedBit.toffoliStep sa sb cmp pre))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne a r sa cmp
      (scratchABit_compareBit_wire_ne tail counterWidth),
    EncodedBit.cnotStep_get_of_target_ne h sb cmp
      (scratchBBit_compareBit_wire_ne tail counterWidth),
    EncodedBit.toffoliStep_get_target sa sb cmp,
    hpre cmp (compareBit_counterCarryInBit_wire_ne
      tail counterWidth).symm,
    hpre sa (scratchABit_counterCarryInBit_wire_ne
      tail counterWidth).symm,
    hpre sb (scratchBBit_counterCarryInBit_wire_ne
      tail counterWidth).symm]

/-- Exact second-scratch effect of the selected-history cleanup CNOT. -/
theorem branchResidueCleanupStep_get_scratchB
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (scratchBBit tail counterWidth).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      ((scratchBBit tail counterWidth).get x ^^
        (historyBit tail counterWidth roundIndex).get x) := by
  let a := activeBit tail counterWidth
  let c := counterCarryInBit tail counterWidth
  let cmp := compareBit tail counterWidth
  let sa := scratchABit tail counterWidth
  let sb := scratchBBit tail counterWidth
  let h := historyBit tail counterWidth roundIndex
  let r := rCoeffLowBit tail counterWidth
  let pre := EncodedBit.cnotStep sb c
    (EncodedBit.cnotStep sa c (EncodedBit.cnotStep a c x))
  let compared := EncodedBit.toffoliStep sa sb cmp pre
  have hpre (observed : EncodedBit (encoding tail.succ counterWidth))
      (hne : c.wire ≠ observed.wire) :
      observed.get pre = observed.get x := by
    simp only [pre]
    rw [EncodedBit.cnotStep_get_of_target_ne sb c observed hne,
      EncodedBit.cnotStep_get_of_target_ne sa c observed hne,
      EncodedBit.cnotStep_get_of_target_ne a c observed hne]
  have hcompared (observed : EncodedBit (encoding tail.succ counterWidth))
      (hc : c.wire ≠ observed.wire)
      (hcmp : cmp.wire ≠ observed.wire) :
      observed.get compared = observed.get x := by
    simp only [compared]
    rw [EncodedBit.toffoliStep_get_of_target_ne sa sb cmp observed hcmp]
    exact hpre observed hc
  change sb.get (EncodedBit.toffoliStep a r sa
    (EncodedBit.cnotStep h sb compared)) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne a r sa sb
      (scratchABit_scratchBBit_wire_ne tail counterWidth),
    EncodedBit.cnotStep_get_target h sb,
    hcompared sb (scratchBBit_counterCarryInBit_wire_ne
      tail counterWidth).symm
      (scratchBBit_compareBit_wire_ne tail counterWidth).symm,
    hcompared h (historyBit_counterCarryInBit_wire_ne
      tail counterWidth roundIndex).symm
      (compareBit_historyBit_wire_ne tail counterWidth roundIndex)]

/-- Exact first-scratch effect of the active-controlled coefficient-parity
cleanup Toffoli. -/
theorem branchResidueCleanupStep_get_scratchA
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (scratchABit tail counterWidth).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      ((scratchABit tail counterWidth).get x ^^
        ((activeBit tail counterWidth).get x &&
          (rCoeffLowBit tail counterWidth).get x)) := by
  let a := activeBit tail counterWidth
  let c := counterCarryInBit tail counterWidth
  let cmp := compareBit tail counterWidth
  let sa := scratchABit tail counterWidth
  let sb := scratchBBit tail counterWidth
  let h := historyBit tail counterWidth roundIndex
  let r := rCoeffLowBit tail counterWidth
  let pre := EncodedBit.cnotStep sb c
    (EncodedBit.cnotStep sa c (EncodedBit.cnotStep a c x))
  let compared := EncodedBit.toffoliStep sa sb cmp pre
  let beforeFinal := EncodedBit.cnotStep h sb compared
  have hpre (observed : EncodedBit (encoding tail.succ counterWidth))
      (hne : c.wire ≠ observed.wire) :
      observed.get pre = observed.get x := by
    simp only [pre]
    rw [EncodedBit.cnotStep_get_of_target_ne sb c observed hne,
      EncodedBit.cnotStep_get_of_target_ne sa c observed hne,
      EncodedBit.cnotStep_get_of_target_ne a c observed hne]
  have hbefore (observed : EncodedBit (encoding tail.succ counterWidth))
      (hc : c.wire ≠ observed.wire)
      (hcmp : cmp.wire ≠ observed.wire)
      (hsb : sb.wire ≠ observed.wire) :
      observed.get beforeFinal = observed.get x := by
    simp only [beforeFinal, compared]
    rw [EncodedBit.cnotStep_get_of_target_ne h sb observed hsb,
      EncodedBit.toffoliStep_get_of_target_ne sa sb cmp observed hcmp]
    exact hpre observed hc
  change sa.get (EncodedBit.toffoliStep a r sa beforeFinal) = _
  rw [EncodedBit.toffoliStep_get_target a r sa,
    hbefore sa (scratchABit_counterCarryInBit_wire_ne
      tail counterWidth).symm
      (scratchABit_compareBit_wire_ne tail counterWidth).symm
      (scratchABit_scratchBBit_wire_ne tail counterWidth).symm,
    hbefore a (activeBit_counterCarryInBit_wire_ne
      tail counterWidth).symm
      (activeBit_compareBit_wire_ne tail counterWidth).symm
      (activeBit_scratchBBit_wire_ne tail counterWidth).symm,
    hbefore r (rCoeffLowBit_counterCarryInBit_wire_ne
      tail counterWidth).symm
      (compareBit_rCoeffLowBit_wire_ne tail counterWidth)
      (rCoeffLowBit_scratchBBit_wire_ne tail counterWidth).symm]

/-- The physical endpoint asserted after branch-residue cleanup. -/
structure BranchResidueCleanEndpoint (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop where
  counterCarry : (counterCarryInBit tail counterWidth).get x = false
  compare : (compareBit tail counterWidth).get x = false
  scratchA : (scratchABit tail counterWidth).get x = false
  scratchB : (scratchBBit tail counterWidth).get x = false

/-- The six physical cleanup gates erase every branch residue described by
the certificate; this is a statement about the actual encoded bits, not a
masked semantic readout. -/
theorem branchResidueCleanupStep_cleanEndpoint
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (cert : BranchResidueCertificate tail counterWidth roundIndex x) :
    BranchResidueCleanEndpoint tail counterWidth
      (branchResidueCleanupStep tail counterWidth roundIndex x) := by
  constructor
  · rw [branchResidueCleanupStep_get_counterCarry,
      cert.counterCarry]
    cases (activeBit tail counterWidth).get x <;>
      cases (scratchABit tail counterWidth).get x <;>
      cases (scratchBBit tail counterWidth).get x <;> rfl
  · rw [branchResidueCleanupStep_get_compare, cert.compare]
    cases (scratchABit tail counterWidth).get x <;>
      cases (scratchBBit tail counterWidth).get x <;> rfl
  · rw [branchResidueCleanupStep_get_scratchA, cert.auxiliary]
    cases (activeBit tail counterWidth).get x <;>
      cases (rCoeffLowBit tail counterWidth).get x <;> rfl
  · rw [branchResidueCleanupStep_get_scratchB, cert.history]
    cases (historyBit tail counterWidth roundIndex).get x <;> rfl

/-- The branch-residue cleanup touches exactly its four target wires.  This
generic preservation lemma is the physical bridge used to reconstruct source
registers, persistent history, and every remaining work word bit-by-bit. -/
theorem branchResidueCleanupStep_get_of_targets_ne
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (observed : EncodedBit (encoding tail.succ counterWidth))
    (hcarry :
      (counterCarryInBit tail counterWidth).wire ≠ observed.wire)
    (hcompare : (compareBit tail counterWidth).wire ≠ observed.wire)
    (hscratchA : (scratchABit tail counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit tail counterWidth).wire ≠ observed.wire) :
    observed.get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      observed.get x := by
  unfold branchResidueCleanupStep branchResidueCleanupGates
  change observed.get
      (EncodedBit.toffoliStep
        (activeBit tail counterWidth) (rCoeffLowBit tail counterWidth)
        (scratchABit tail counterWidth)
        (EncodedBit.cnotStep
          (historyBit tail counterWidth roundIndex)
          (scratchBBit tail counterWidth)
          (EncodedBit.toffoliStep
            (scratchABit tail counterWidth) (scratchBBit tail counterWidth)
            (compareBit tail counterWidth)
            (EncodedBit.cnotStep
              (scratchBBit tail counterWidth)
              (counterCarryInBit tail counterWidth)
              (EncodedBit.cnotStep
                (scratchABit tail counterWidth)
                (counterCarryInBit tail counterWidth)
                (EncodedBit.cnotStep
                  (activeBit tail counterWidth)
                  (counterCarryInBit tail counterWidth) x)))))) =
    observed.get x
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (activeBit tail counterWidth) (rCoeffLowBit tail counterWidth)
      (scratchABit tail counterWidth) observed hscratchA]
  rw [EncodedBit.cnotStep_get_of_target_ne
      (historyBit tail counterWidth roundIndex)
      (scratchBBit tail counterWidth) observed hscratchB]
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (scratchABit tail counterWidth) (scratchBBit tail counterWidth)
      (compareBit tail counterWidth) observed hcompare]
  rw [EncodedBit.cnotStep_get_of_target_ne
      (scratchBBit tail counterWidth)
      (counterCarryInBit tail counterWidth) observed hcarry]
  rw [EncodedBit.cnotStep_get_of_target_ne
      (scratchABit tail counterWidth)
      (counterCarryInBit tail counterWidth) observed hcarry]
  rw [EncodedBit.cnotStep_get_of_target_ne
      (activeBit tail counterWidth)
      (counterCarryInBit tail counterWidth) observed hcarry]

theorem branchResidueCleanupStep_get_historyBit
    (tail counterWidth : Nat) (roundIndex observed : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (historyBit tail counterWidth observed).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      (historyBit tail counterWidth observed).get x := by
  exact branchResidueCleanupStep_get_of_targets_ne tail counterWidth
    roundIndex x (historyBit tail counterWidth observed)
    (historyBit_counterCarryInBit_wire_ne
      tail counterWidth observed).symm
    (compareBit_historyBit_wire_ne tail counterWidth observed)
    (scratchABit_historyBit_wire_ne tail counterWidth observed)
    (by
      simpa only [ne_eq] using
        (historyBit_scratchBBit_wire_ne
          tail counterWidth observed).symm)

private structure ReusableWorkspaceSnapshot (tail counterWidth : Nat) where
  comparisonWork : ComparisonWork tail.succ
  coefficientWork : CoeffAdderWork tail.succ
  counterSource : Word counterWidth
  counterCarryWork : CounterIncrementCarryWork counterWidth
  path : Bool
  control : Bool
  routeHistory : Word (2 * tail.succ)

private def reusableWorkspaceSnapshot (tail counterWidth : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    ReusableWorkspaceSnapshot tail counterWidth where
  comparisonWork := x.1.1.1.1.1.2
  coefficientWork := x.1.1.1.1.2
  counterSource := x.1.1.1.2.1
  counterCarryWork := x.1.1.1.2.2.2
  path := x.1.1.2
  control := x.1.2
  routeHistory := x.2

/-- Cleanup writes only the four residue targets, so all reusable ancillas,
the working path, and clean control are preserved as one structural
projection. -/
private theorem branchResidueCleanupStep_reusableWorkspaceSnapshot
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    reusableWorkspaceSnapshot tail counterWidth
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      reusableWorkspaceSnapshot tail counterWidth x := by
  unfold branchResidueCleanupStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [branchResidueCleanupGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro y
    rfl

theorem branchResidueCleanupStep_reusableWorkspaceClean
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hclean : ReusableWorkspaceClean tail counterWidth x) :
    ReusableWorkspaceClean tail counterWidth
      (branchResidueCleanupStep tail counterWidth roundIndex x) := by
  have hsnapshot :=
    branchResidueCleanupStep_reusableWorkspaceSnapshot
      tail counterWidth roundIndex x
  constructor
  · exact (congrArg ReusableWorkspaceSnapshot.comparisonWork hsnapshot).trans
      hclean.comparisonWork
  · exact (congrArg ReusableWorkspaceSnapshot.coefficientWork hsnapshot).trans
      hclean.coefficientWork
  · exact (congrArg ReusableWorkspaceSnapshot.counterSource hsnapshot).trans
      hclean.counterSource
  · exact
      (congrArg ReusableWorkspaceSnapshot.counterCarryWork hsnapshot).trans
        hclean.counterCarryWork
  · exact (congrArg ReusableWorkspaceSnapshot.control hsnapshot).trans
      hclean.control

theorem branchResidueCleanupStep_get_path
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (workingPathBit tail counterWidth).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      (workingPathBit tail counterWidth).get x := by
  have hsnapshot :=
    branchResidueCleanupStep_reusableWorkspaceSnapshot
      tail counterWidth roundIndex x
  exact congrArg ReusableWorkspaceSnapshot.path hsnapshot

theorem branchResidueCleanupStep_get_route
    (tail counterWidth : Nat) (roundIndex observed : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (routeHistoryBit tail counterWidth observed).get
        (branchResidueCleanupStep tail counterWidth roundIndex x) =
      (routeHistoryBit tail counterWidth observed).get x := by
  have hsnapshot :=
    branchResidueCleanupStep_reusableWorkspaceSnapshot
      tail counterWidth roundIndex x
  have hroute :=
    congrArg ReusableWorkspaceSnapshot.routeHistory hsnapshot
  have hrouteWord :
      (branchResidueCleanupStep tail counterWidth roundIndex x).2 = x.2 := by
    simpa [reusableWorkspaceSnapshot] using hroute
  change
    (BinaryLabelEncoding.finIdentityBit (2 * tail.succ) observed).get
        (branchResidueCleanupStep tail counterWidth roundIndex x).2 =
      (BinaryLabelEncoding.finIdentityBit (2 * tail.succ) observed).get x.2
  rw [hrouteWord]

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
