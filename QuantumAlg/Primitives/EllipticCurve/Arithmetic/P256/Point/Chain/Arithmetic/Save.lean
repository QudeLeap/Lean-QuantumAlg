/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Admitted
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Readout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Choice
import all QuantumAlg.Components.Encoded.BitGates.Word.CopyValue

/-!
# Actual active product and inactive numerator save on the original words

The same program first performs clean-target Horner multiplication, then
an actual negatively selected numerator-to-accumulator XOR. The selector
is either the whole-digit enable F560 or the real normal selector N837.
Inactive source and numerator words are arbitrary; their quantum information
is copied into the existing clean accumulator before the later measurement.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

/-- These are separate actual physical controls with different mathematical meanings. -/
inductive Selector where
  | enable
  | normal
deriving DecidableEq

def selectorBit (ports : PortAssignment) : Selector → EncodedBit (Placement.restEncoding ports)
  | .enable => Native.BorrowedControl.controlBit ports
  | .normal => Native.controlBit ports .normal

namespace Save

variable {Rest : Type} (rest : BinaryLabelEncoding Rest)

private abbrev Saved := Word × Rest

private abbrev savedEncoding := Accumulate.Square.savedEncoding rest

private def sourceWord : EncodedBit.Word (operandEncoding (savedEncoding rest)) width :=
  Accumulate.Square.targetWord rest

private def targetBit (index : Fin width) : EncodedBit (operandEncoding (savedEncoding rest)) :=
  BinaryLabelEncoding.prodLeftBit ModularAddition.Controlled.selectorEncoding (savedEncoding rest)
    (BinaryLabelEncoding.prodLeftBit ModularAddition.encoding
      ModularAddition.Controlled.flagEncoding (ModularAddition.targetBit index))

private def targetWord : EncodedBit.Word (operandEncoding (savedEncoding rest)) width :=
  ⟨targetBit rest⟩

private lemma target_get (index : Fin width) (state : OperandRegisters (Saved (Rest := Rest))) :
    (targetBit rest index).get state = state.1.1.1.2.val.testBit index.val := by
  change (MAU.Addition.TTK.rightBit width index).get state.1.1.1 = _
  exact MAU.Addition.TTK.ttkRightBit_get width index state.1.1.1

private lemma source_get (index : Fin width) (state : OperandRegisters (Saved (Rest := Rest))) :
    ((sourceWord rest).bit index).get state = state.2.1.val.testBit index.val :=
  (Accumulate.Square.multiplier rest).reads state.2 index

private lemma source_target_ne (source target : Fin width) :
    ((sourceWord rest).bit source).wire ≠ ((targetWord rest).bit target).wire := by
  intro same
  have positions := congrArg Fin.val same
  change 515 + (width - 1 - source.val) = width + (width - 1 - target.val) at positions
  have bounded := target.isLt
  change target.val < 256 at bounded
  change 515 + (256 - 1 - source.val) = 256 + (256 - 1 - target.val) at positions
  omega

private lemma target_distinct (left right : Fin width) (different : left ≠ right) :
    ((targetWord rest).bit left).wire ≠ ((targetWord rest).bit right).wire := by
  intro same
  apply different
  apply Fin.ext
  have positions := congrArg Fin.val same
  change width + (width - 1 - left.val) = width + (width - 1 - right.val) at positions
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

private def copyGates : List (GateSpec (operandEncoding (savedEncoding rest))) :=
  EncodedBit.Word.xorIntoGates (sourceWord rest) (targetWord rest)
    (fun index => source_target_ne rest index index)

private lemma copy_clean (source multiplier : Word) (reduction latch work : Bool)
    (retained : Rest) :
    stepList (copyGates rest)
        ((((source, zeroWord), reduction), (latch, work)), (multiplier, retained)) =
      ((((source, multiplier), reduction), (latch, work)), (multiplier, retained)) := by
  exact EncodedBit.Word.xorIntoStep_eq_set_of_clean
    (sourceWord rest) (targetWord rest) (fun index => source_target_ne rest index index)
    (fun state => state.1.1.1.2)
    (fun state => ((state.1.1.1.1, state.1.1.2), (state.1.2, state.2)))
    (fun frame target => ((((frame.1.1, target), frame.1.2), frame.2.1), frame.2.2))
    (fun _ => rfl) (target_get rest) (target_distinct rest)
    (fun source target => (source_target_ne rest source target).symm)
    (fun _ _ => rfl) _ multiplier
    (by apply Fin.ext; rfl) (fun index => source_get rest index _)

private def controlBit (selector : EncodedBit rest) :
    EncodedBit (operandEncoding (savedEncoding rest)) :=
  operandSavedBit (savedEncoding rest) (Accumulate.Square.outerBit rest selector)

private def workBit : EncodedBit (operandEncoding (savedEncoding rest)) :=
  operandLatchBit (savedEncoding rest)

private lemma control_copy (selector : EncodedBit rest)
    (gate : GateSpec (operandEncoding (savedEncoding rest))) (present : gate ∈ copyGates rest) :
    bitDisjoint (controlBit rest selector) gate := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  constructor
  · exact (Accumulate.Square.outer_multiplier_ne rest selector index).symm
  · intro same
    have positions := congrArg Fin.val same
    change width + (width - 1 - index.val) = 515 + (width + selector.wire.val) at positions
    have bounded := index.isLt
    change index.val < 256 at bounded
    change 256 + (256 - 1 - index.val) = 515 + (256 + selector.wire.val) at positions
    omega

private lemma work_copy (gate : GateSpec (operandEncoding (savedEncoding rest)))
    (present : gate ∈ copyGates rest) : bitDisjoint (workBit rest) gate := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  constructor <;> intro same <;> have positions := congrArg Fin.val same
  · change 515 + (width - 1 - index.val) = 513 at positions
    omega
  · change width + (width - 1 - index.val) = 513 at positions
    have bounded := index.isLt
    change index.val < 256 at bounded
    change 256 + (256 - 1 - index.val) = 513 at positions
    omega

private lemma control_work (selector : EncodedBit rest) :
    (controlBit rest selector).wire ≠ (workBit rest).wire :=
  operandSaved_latch_ne (savedEncoding rest) (Accumulate.Square.outerBit rest selector)

/-- The shared control remains a real conflict across the sequential word-copy Toffolis. -/
def negativeCopyGates (selector : EncodedBit rest) :
    List (GateSpec (operandEncoding (savedEncoding rest))) :=
  choiceGates (controlBit rest selector) (workBit rest) (copyGates rest) []
    (control_copy rest selector) (work_copy rest) (by simp) (by simp)
    (control_work rest selector)

private lemma negativeCopy_step (selector : EncodedBit rest)
    (state : OperandRegisters (Saved (Rest := Rest))) :
    stepList (negativeCopyGates rest selector) state =
      if selector.get state.2.2 then state else stepList (copyGates rest) state :=
  choiceGates_step (controlBit rest selector) (workBit rest) (copyGates rest) []
    (control_copy rest selector) (work_copy rest) (by simp) (by simp)
    (control_work rest selector) state

def negativeCopyProgram (selector : EncodedBit rest) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (negativeCopyGates rest selector)

private def rawCleanProgram (selector : EncodedBit rest) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  Horner.cleanProgram (savedEncoding rest) (Accumulate.Square.multiplier rest).quantum
    (Accumulate.Square.outerBit rest selector) (Accumulate.Square.outer_multiplier_ne rest selector)

/-- The original clean A is filled by the active product or by the inactive original Y. -/
def rawProgram (selector : EncodedBit rest) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  (rawCleanProgram rest selector).seq (negativeCopyProgram rest selector)

/-- Only the active branch asks for modular arithmetic; the other branch saves the original Y. -/
def savedWord (source multiplier : Word) (selected : Bool) : Word :=
  if selected then Horner.productWord source multiplier true else multiplier

private def rawKet (state : OperandRegisters (Saved (Rest := Rest))) :=
  NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((operandEncoding (savedEncoding rest)).encode state))

private lemma admitted_cases {Result : Type} (actual expected : Result) (selected : Bool)
    (Premise : Prop) (admitted : selected = true → Premise)
    (active : Premise → actual = expected) (inactive : selected = false → actual = expected) :
    actual = expected := by
  cases selected with
  | false => exact inactive rfl
  | true => exact active (admitted rfl)

private lemma product_false (source multiplier : Word) :
    Horner.productWord source multiplier false = zeroWord := by
  apply Fin.ext
  rfl

private lemma rawClean_product (selector : EncodedBit rest)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word) (retained : Rest)
    (admitted : selector.get retained = true → Canonical source) :
    (rawCleanProgram rest selector).applyNormalized environment
        (rawKet rest ((((source, zeroWord), false), (false, false)), (multiplier, retained))) =
      rawKet rest ((((source, Horner.productWord source multiplier (selector.get retained)), false),
        (false, false)), (multiplier, retained)) := by
  apply admitted_cases _ _ (selector.get retained) (Canonical source) admitted
  · intro canonical
    exact Horner.cleanProgram_product (savedEncoding rest)
      (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
      (Accumulate.Square.outer_multiplier_ne rest selector) environment source canonical
      (multiplier, retained)
  · intro disabled
    have actual := Horner.cleanProgram_inactive (savedEncoding rest)
      (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
      (Accumulate.Square.outer_multiplier_ne rest selector) environment source
      (multiplier, retained) disabled
    have output : Horner.productWord source multiplier (selector.get retained) = zeroWord := by
      rw [disabled]
      exact product_false source multiplier
    exact actual.trans (congrArg (fun target : Word => rawKet rest
      ((((source, target), false), (false, false)), (multiplier, retained))) output).symm

private lemma negativeCopy_saved (selector : EncodedBit rest) (source multiplier : Word)
    (retained : Rest) :
    stepList (negativeCopyGates rest selector)
        ((((source, Horner.productWord source multiplier (selector.get retained)), false),
          (false, false)), (multiplier, retained)) =
      ((((source, savedWord source multiplier (selector.get retained)), false), (false, false)),
        (multiplier, retained)) := by
  rw [negativeCopy_step]
  change (if selector.get retained then _ else _) = _
  cases selected : selector.get retained with
  | false =>
      simp only [Bool.false_eq_true, if_false, savedWord, product_false]
      exact copy_clean rest source multiplier false false false retained
  | true => rfl

/-- Actual phase-exact save retains every original source/flag/caller coordinate. -/
lemma rawProgram_apply (selector : EncodedBit rest)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word) (retained : Rest)
    (admitted : selector.get retained = true → Canonical source) :
    (rawProgram rest selector).applyNormalized environment
        (rawKet rest ((((source, zeroWord), false), (false, false)), (multiplier, retained))) =
      rawKet rest ((((source, savedWord source multiplier (selector.get retained)), false),
        (false, false)), (multiplier, retained)) := by
  have first := rawClean_product rest selector environment source multiplier retained admitted
  have second := (realizesList (QubitLayout.canonical _) .empty
    (negativeCopyGates rest selector) environment).apply_encoded_ket
      ((((source, Horner.productWord source multiplier (selector.get retained)), false),
        (false, false)), (multiplier, retained))
  exact UnitaryCircuit.applyNormalized_seq_of_eq first
    (second.trans (congrArg (rawKet rest)
      (negativeCopy_saved rest selector source multiplier retained)))

def program (ports : PortAssignment) (selector : Selector) : Native.Circuit :=
  (Placement.layout ports).place
    (rawProgram (Placement.restEncoding ports) (selectorBit ports selector))

/-- Original X is the source, A the existing clean accumulator, and Y the retained numerator. -/
def ports : PortAssignment where
  source := .work2
  target := .work1
  multiplier := .numerator
  source_target := by decide
  source_multiplier := by decide
  target_multiplier := by decide

lemma program_apply (assignment : PortAssignment) (selector : Selector)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (retained : Placement.Rest assignment)
    (admitted : (selectorBit assignment selector).get retained = true → Canonical source) :
    (program assignment selector).applyNormalized environment
        (Native.ket (Native.arithmeticState assignment source zeroWord multiplier retained)) =
      Native.ket (Native.arithmeticState assignment source
        (savedWord source multiplier ((selectorBit assignment selector).get retained))
        multiplier retained) :=
  (Placement.layout assignment).place_ket_of_eq _ _ _
    (rawProgram_apply (Placement.restEncoding assignment) (selectorBit assignment selector)
      environment source multiplier retained admitted)

/-- Mixed coherent active/inactive labels retain the same complete external Reference. -/
lemma program_reference (assignment : PortAssignment) (selector : Selector)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source multiplier : Index → Word)
    (retained : Index → Placement.Rest assignment)
    (admitted : ∀ index, (selectorBit assignment selector).get (retained index) = true →
      Canonical (source index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator (program assignment selector)
      environment Reference)
        (Native.referenceVector (fun index => Native.arithmeticState assignment (source index)
          zeroWord (multiplier index) (retained index)) reference amplitude) =
      Native.referenceVector (fun index => Native.arithmeticState assignment (source index)
        (savedWord (source index) (multiplier index)
          ((selectorBit assignment selector).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  Native.coherent_of_basis _ environment _ _ (fun index => program_apply assignment selector
    environment (source index) (multiplier index) (retained index) (admitted index))
    reference amplitude

end Save

end

end Arithmetic

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
