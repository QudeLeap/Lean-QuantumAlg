/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body

/-!
# The same actual arithmetic bodies on original coefficient wires

The choice of low or signed arithmetic is a public source-instruction
parameter. Full runtime quantum addresses remain in the same physical
registers. Original Work1 supplies the little-endian coefficient addend,
and original Work2 receives the sum; signed mode retains the same
arbitrary original Sign [LYL+26, sec_EEA/sub_regshare.tex:17,20,291-294].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Both actual source bodies use the identical complete original register and pool carrier. -/
def sourceProgram (width : Nat) : Bool → UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum
  | false => ArithmeticWindow.program width
  | true => ArithmeticSignedWindow.program width

/-- Independent low or carry-output addition on the declared actual ordered source window. -/
def sourceStep (width length : Nat) (fits : length ≤ width + 3) : Bool → Data width → Data width
  | false => (ArithmeticWindow.placement width length fits).step
  | true => ArithmeticTop.windowStep width length fits

private lemma sourceStep_length_congr (width left right : Nat)
    (leftFits : left ≤ width + 3) (rightFits : right ≤ width + 3)
    (signed : Bool) (same : left = right) :
    sourceStep width left leftFits signed = sourceStep width right rightFits signed := by
  subst right
  rfl

/-- The mathematical word operation at original coefficient positions with its full complement. -/
def windowStep (width length : Nat) (fits : length ≤ width + 3) (signed : Bool) :
    Data width → Data width :=
  (CoefficientFrame.placement width).step (sourceStep width length fits signed)

/-- Every native source gate is emitted at its declared original coefficient positions. -/
def program (width : Nat) (signed : Bool) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (CoefficientFrame.placement width).place (sourceProgram width signed)

/-- Full coefficient arithmetic retains the quantum address and restores the complete pool. -/
lemma program_apply_window (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (program width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          windowStep width (state.2.1.toNat + 1) (by omega) signed state else state))) := by
  let grouped := (CoefficientFrame.placement width).grouping state
  have pool : grouped.2 = state.2 := CoefficientFrame.grouped_pool width state
  have address : grouped.2.1 = state.2.1 := congrArg Prod.fst pool
  have groupedClean : grouped.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans clean
  have groupedZero : grouped.2.2.2 = false :=
    (congrArg (fun value : Pool width => value.2.2) pool).trans zero
  have groupedWithin : grouped.2.1.toNat < width + 3 := by rw [address]; exact within
  have actual : (sourceProgram width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode grouped))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if grouped.1.control then
          sourceStep width (state.2.1.toNat + 1) (by omega) signed grouped else grouped))) := by
    have original : (sourceProgram width signed).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode grouped))) =
        NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode (if grouped.1.control then
            sourceStep width (grouped.2.1.toNat + 1) (by omega) signed grouped else grouped))) := by
      cases signed with
      | false =>
          exact ArithmeticWindow.program_apply_window width positive environment grouped
            groupedClean groupedZero groupedWithin
      | true =>
          exact ArithmeticSignedWindow.program_apply_window width positive environment grouped
            groupedClean groupedZero groupedWithin
    rw [sourceStep_length_congr width (grouped.2.1.toNat + 1) (state.2.1.toNat + 1)
      (by omega) (by omega) signed
      (congrArg (fun value : BitVec (ScanMetadata.addressWidth width) => value.toNat + 1) address)]
      at original
    exact original
  have placed := (CoefficientFrame.placement width).place_ket_of_eq (sourceProgram width signed)
    grouped _ actual
  have restoredInput : (CoefficientFrame.placement width).grouping.symm grouped = state :=
    (CoefficientFrame.placement width).grouping.symm_apply_apply state
  have control : grouped.1.control = state.1.control :=
    CoefficientFrame.grouped_control width state
  rw [restoredInput, control] at placed
  cases selected : state.1.control <;>
    simpa only [program, selected, Bool.false_eq_true, if_false, if_true, windowStep,
      FullPlacement.step, grouped, Equiv.symm_apply_apply] using placed

/-- Actual static placement preserves every native count of either original source body. -/
lemma program_eventCost (width : Nat) (signed : Bool) :
    (program width signed).eventCost = (sourceProgram width signed).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    CoefficientFrame.place_eventTrace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Actual dependencies and default quantum time remain those of the same emitted source body. -/
lemma program_quantumTime (width : Nat) (signed : Bool) :
    (program width signed).evaluatedEventDepth Resource.Event.quantumDuration =
      (sourceProgram width signed).evaluatedEventDepth Resource.Event.quantumDuration :=
  CoefficientFrame.place_quantumTime width (sourceProgram width signed)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow
