/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Core.Base.UnitaryCircuit.Space
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Exponent-controlled ECADD cascade

This module places `2 * t` literal controlled-ECADD circuits on one shared
point-and-workspace tail.  Block `i` uses exponent wire `i` as its leading
control, while every non-control ECADD wire is mapped to the same tail range.
The blocks are composed sequentially, so the workspace is reused rather than
replicated.

The construction and resource theorems are unconditional.  Its public ECADD
semantics remains the generic affine semantics of
`ControlledPointAddition.program_clean_ket`; exceptional inputs require a
separate probability argument and are not hidden in this module.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication
namespace ExponentControlledECADDCascade

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

variable {E : PrimeFieldShortWeierstrass params.modulus.val}

/-- The non-control suffix of one canonical controlled-ECADD carrier. -/
def tailWidth : Nat :=
  ControlledPointAddition.logicalQubitCount params.width - 1

/-- The canonical ECADD width is one leading control plus its reusable tail. -/
theorem rawEncoding_width_eq_one_add_tailWidth :
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width =
      1 + tailWidth := by
  rw [GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding_width_exact]
  unfold tailWidth ControlledPointAddition.logicalQubitCount
    Arithmetic.ModularInversion.physicalWidthFor
    Arithmetic.ModularInversion.counterWidthFor
  omega

/-- Closed form for one leading control and the reusable ECADD tail. -/
theorem one_add_tailWidth_eq_closed :
    1 + tailWidth =
      37 * params.width + 27 + 3 * Nat.clog 2 (2 * params.width) := by
  unfold tailWidth ControlledPointAddition.logicalQubitCount
  omega

/-- The complete carrier consists of `2 * t` controls and one ECADD tail. -/
def logicalQubitCount (t : Nat) : Nat :=
  2 * t + tailWidth

/-- Direct closed form for the complete shared-tail carrier. -/
theorem logicalQubitCount_eq_closed (t : Nat) :
    logicalQubitCount (params := params) t =
      2 * t + 37 * params.width + 26 +
        3 * Nat.clog 2 (2 * params.width) := by
  unfold logicalQubitCount tailWidth ControlledPointAddition.logicalQubitCount
  omega

/-- Transport a flat computational-basis label across equality of widths. -/
def widthCastLabel {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (label : Fin (2 ^ sourceWidth)) : Fin (2 ^ targetWidth) :=
  Equiv.cast (congrArg (fun width => Fin (2 ^ width)) widthEquality) label

omit params in
@[simp] theorem widthCastLabel_val {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (label : Fin (2 ^ sourceWidth)) :
    (widthCastLabel widthEquality label).val = label.val := by
  subst targetWidth
  rfl

omit params in
/-- Two width transports into the same target agree whenever their source
labels have the same underlying natural value. -/
theorem widthCastLabel_eq_of_val
    {sourceWidth otherSourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (otherWidthEquality : otherSourceWidth = targetWidth)
    (label : Fin (2 ^ sourceWidth))
    (otherLabel : Fin (2 ^ otherSourceWidth))
    (hval : label.val = otherLabel.val) :
    widthCastLabel widthEquality label =
      widthCastLabel otherWidthEquality otherLabel := by
  apply Fin.ext
  rw [widthCastLabel_val, widthCastLabel_val]
  exact hval

omit params in
/-- Append a right-hand label after transporting only that field's width. -/
def prodWidthCastLabel
    {leftWidth sourceRightWidth targetRightWidth : Nat}
    (rightWidthEquality : sourceRightWidth = targetRightWidth)
    (leftLabel : Fin (2 ^ leftWidth))
    (rightLabel : Fin (2 ^ sourceRightWidth)) :
    Fin (2 ^ (leftWidth + targetRightWidth)) :=
  prodEquiv (leftLabel, widthCastLabel rightWidthEquality rightLabel)

omit params in
/-- Width casts commute with appending a right-hand binary field.  The proof is
symbolic in both widths, so users do not need to normalize the cardinality of
the resulting basis-label type. -/
theorem widthCastLabel_prodEquiv_right
    {leftWidth sourceRightWidth targetRightWidth : Nat}
    (rightWidthEquality : sourceRightWidth = targetRightWidth)
    (fullWidthEquality :
      leftWidth + sourceRightWidth = leftWidth + targetRightWidth)
    (leftLabel : Fin (2 ^ leftWidth))
    (rightLabel : Fin (2 ^ sourceRightWidth)) :
    widthCastLabel fullWidthEquality (prodEquiv (leftLabel, rightLabel)) =
      prodWidthCastLabel rightWidthEquality leftLabel rightLabel := by
  apply Fin.ext
  simp [prodWidthCastLabel, prodEquiv, rightWidthEquality]

omit params in
/-- Width casts preserve the flat label when three consecutive fields are
reassociated around the leading field. -/
theorem widthCastLabel_prodEquiv_assoc {middle right tail : Nat}
    (tailWidthEquality : middle + right = tail)
    (fullWidthEquality : 1 + middle + right = 1 + tail)
    (leading : Fin 2) (middleLabel : Fin (2 ^ middle))
    (rightLabel : Fin (2 ^ right)) :
    widthCastLabel fullWidthEquality
        (prodEquiv (prodEquiv (leading, middleLabel), rightLabel)) =
      prodEquiv
        (leading,
          widthCastLabel tailWidthEquality
            (prodEquiv (middleLabel, rightLabel))) := by
  subst tail
  apply Fin.ext
  simp [prodEquiv, pow_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.add_assoc]

/-- Transport a circuit across equality of flat qubit counts.  This changes
only the parenthesization or arithmetic presentation of the width. -/
def widthCastProgram {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (program : UnitaryCircuit (Qubits sourceWidth)) :
    UnitaryCircuit (Qubits targetWidth) :=
  UnitaryCircuit.reindex
    (Equiv.cast (congrArg (fun width => Fin (2 ^ width)) widthEquality))
    program

omit params in
@[simp] theorem widthCastProgram_eventCost {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (program : UnitaryCircuit (Qubits sourceWidth)) :
    (widthCastProgram widthEquality program).eventCost = program.eventCost := by
  simp [widthCastProgram]

omit params in
@[simp] theorem widthCastProgram_evaluatedEventDepth
    {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (assign : Resource.Event .quantum → Nat)
    (program : UnitaryCircuit (Qubits sourceWidth)) :
    (widthCastProgram widthEquality program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  simp [widthCastProgram, UnitaryCircuit.evaluatedEventDepth]

omit params in
@[simp] theorem widthCastProgram_physical_idx
    {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (program : UnitaryCircuit (Qubits sourceWidth)) :
    (widthCastProgram widthEquality program).physical_idx = program.physical_idx := by
  rfl

omit params in
/-- Width transport carries a proved computational-basis endpoint to the
corresponding transported basis labels. -/
theorem widthCastProgram_applyNormalized_ket_of_eq
    {sourceWidth targetWidth : Nat}
    (widthEquality : sourceWidth = targetWidth)
    (program : UnitaryCircuit (Qubits sourceWidth))
    (input output : Fin (2 ^ sourceWidth))
    (happly : program.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (widthCastProgram widthEquality program).applyNormalized
        (NormalizedVector.ket (widthCastLabel widthEquality input)) =
      NormalizedVector.ket (widthCastLabel widthEquality output) := by
  simpa only [widthCastProgram, widthCastLabel] using
    (UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (Equiv.cast (congrArg (fun width => Fin (2 ^ width)) widthEquality))
      program input output happly)

/-- One canonical ECADD body viewed as a leading control followed by its
non-control tail. -/
def controlTailProgram
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (addend : AffinePoint E) :
    UnitaryCircuit (Qubits (1 + tailWidth)) :=
  widthCastProgram rawEncoding_width_eq_one_add_tailWidth
    (ControlledPointAddition.program E addend)

/-- The non-control part of the generic point-addition pipeline. -/
abbrev PipelineTailRegisters : Type :=
  PointAddition.PortFrame.CoreRegisters
      GenericPointAddition.Pipeline.AuxRegisters params.width × Bool

/-- The complete reusable tail: the pipeline suffix followed by exceptional
cleanup storage. -/
abbrev TailRegisters : Type :=
  PipelineTailRegisters ×
    GenericPointAddition.ExceptionalCleanup.Layout.SelectorRegisters

/-- Encoding of the generic-pipeline suffix after its leading public control. -/
def pipelineTailEncoding : BinaryLabelEncoding PipelineTailRegisters :=
  BinaryLabelEncoding.prod
    (PointAddition.PortFrame.coreEncoding
      GenericPointAddition.Pipeline.auxEncoding params.width)
    BinaryLabelEncoding.bool

/-- Encoding of every ECADD wire except its leading public control. -/
def tailEncoding : BinaryLabelEncoding TailRegisters :=
  BinaryLabelEncoding.prod pipelineTailEncoding
    GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding

/-- The reusable tail encoding has exactly the canonical non-control width. -/
theorem tailEncoding_width_eq_tailWidth : tailEncoding.width = tailWidth := by
  unfold tailEncoding pipelineTailEncoding tailWidth
    ControlledPointAddition.logicalQubitCount
  simp only [BinaryLabelEncoding.prod_width,
    PointAddition.PortFrame.coreEncoding_width,
    GenericPointAddition.Pipeline.auxEncoding,
    ParameterizedPointAddition.rawEncoding_width_exact,
    BinaryLabelEncoding.bool_width,
    GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding_width_exact]
  unfold Arithmetic.ModularInversion.physicalWidthFor
    Arithmetic.ModularInversion.counterWidthFor
  omega

/-- Clean semantic contents of the shared tail. -/
def cleanTailRegisters (P : AffinePoint E) : TailRegisters :=
  let boundary := ControlledPointAddition.cleanBoundary false P
  (boundary.1.2, boundary.2)

/-- The clean ECADD tail label, independent of the leading control bit. -/
def cleanTailLabel (P : AffinePoint E) : Fin (2 ^ tailWidth) :=
  widthCastLabel tailEncoding_width_eq_tailWidth
    (tailEncoding.encode (cleanTailRegisters P))

/-- Distinct affine accumulator points have distinct clean shared-tail labels. -/
theorem cleanTailLabel_injective
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] : Function.Injective
      (cleanTailLabel (params := params) (E := E)) := by
  intro left right labelEquality
  have encodedEquality :
      tailEncoding.encode (cleanTailRegisters left) =
        tailEncoding.encode (cleanTailRegisters right) := by
    apply (Equiv.cast (congrArg (fun width => Fin (2 ^ width))
      tailEncoding_width_eq_tailWidth)).injective
    exact labelEquality
  have registersEquality : cleanTailRegisters left = cleanTailRegisters right :=
    tailEncoding.encode_injective encodedEquality
  have wordsEquality :
      GenericPointAddition.Pipeline.pointWords left =
        GenericPointAddition.Pipeline.pointWords right := by
    have extracted := congrArg
      (fun registers : TailRegisters => registers.1.1.1.1)
      registersEquality
    simpa only [cleanTailRegisters, ControlledPointAddition.cleanBoundary,
      GenericPointAddition.ExceptionalCleanup.Layout.translationBoundaryRegisters,
      GenericPointAddition.ExceptionalCleanup.Layout.selectedBoundaryRegisters,
      GenericPointAddition.Pipeline.translationBoundaryRegisters] using extracted
  apply AffinePoint.ext_coordinates
  · apply ZMod.val_injective
    have wordEquality := congrArg (fun words => words.1.val) wordsEquality
    simpa only [GenericPointAddition.Pipeline.pointWords,
      ParameterizedPointAddition.residueWord_val] using wordEquality
  · apply ZMod.val_injective
    have wordEquality := congrArg (fun words => words.2.val) wordsEquality
    simpa only [GenericPointAddition.Pipeline.pointWords,
      ParameterizedPointAddition.residueWord_val] using wordEquality

/-- A reserved tail state distinguished from every clean affine point by the
exceptional-selector bit. -/
def reservedTailRegisters (seed : AffinePoint E) : TailRegisters :=
  ((cleanTailRegisters seed).1, (0, (true, (false, (false, false)))))

/-- Basis label reserved for the group identity, which has no affine
representative. -/
def reservedTailLabel (seed : AffinePoint E) : Fin (2 ^ tailWidth) :=
  widthCastLabel tailEncoding_width_eq_tailWidth
    (tailEncoding.encode (reservedTailRegisters seed))

/-- The reserved identity label cannot equal a clean affine-point label. -/
theorem reservedTailLabel_ne_cleanTailLabel
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    (seed point : AffinePoint E) :
    reservedTailLabel seed ≠ cleanTailLabel point := by
  intro labelEquality
  have encodedEquality :
      tailEncoding.encode (reservedTailRegisters seed) =
        tailEncoding.encode (cleanTailRegisters point) := by
    apply (Equiv.cast (congrArg (fun width => Fin (2 ^ width))
      tailEncoding_width_eq_tailWidth)).injective
    exact labelEquality
  have registersEquality :
      reservedTailRegisters seed = cleanTailRegisters point :=
    tailEncoding.encode_injective encodedEquality
  have selectorEquality := congrArg
    (fun registers : TailRegisters => registers.2.2.1) registersEquality
  have impossible : true = false := by
    simpa only [reservedTailRegisters, cleanTailRegisters,
      ControlledPointAddition.cleanBoundary,
      GenericPointAddition.ExceptionalCleanup.Layout.translationBoundaryRegisters,
      GenericPointAddition.ExceptionalCleanup.Layout.selectedBoundaryRegisters] using
        selectorEquality
  cases impossible

/-- Clean ECADD boundary encoded on the one-control-plus-tail presentation. -/
def rawCleanLabel (control : Bool) (P : AffinePoint E) :
    Fin (2 ^ (1 + tailWidth)) :=
  prodEquiv
    (BinaryLabelEncoding.bool.encode control, cleanTailLabel P)

/-- Reassociating the concrete raw encoding yields the canonical leading
control and reusable-tail label. -/
theorem cast_rawEncoding_encode_cleanBoundary
    (control : Bool) (P : AffinePoint E) :
    widthCastLabel rawEncoding_width_eq_one_add_tailWidth
        (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary control P)) =
      rawCleanLabel control P := by
  let tail := cleanTailRegisters P
  have hsource :
      GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary control P) =
        prodEquiv
          (prodEquiv
            (BinaryLabelEncoding.bool.encode control,
              pipelineTailEncoding.encode tail.1),
            GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.encode
              tail.2) := by
    cases control <;> rfl
  have htail :
      pipelineTailEncoding.width +
          GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.width =
        tailWidth := by
    simpa only [tailEncoding, BinaryLabelEncoding.prod_width] using
      tailEncoding_width_eq_tailWidth
  have hfull :
      1 + pipelineTailEncoding.width +
          GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.width =
        1 + tailWidth := by
    omega
  have hfullCast :
      widthCastLabel rawEncoding_width_eq_one_add_tailWidth
          (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
            (ControlledPointAddition.cleanBoundary control P)) =
        widthCastLabel hfull
          (prodEquiv
            (prodEquiv
              (BinaryLabelEncoding.bool.encode control,
                pipelineTailEncoding.encode tail.1),
              GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.encode
                tail.2)) := by
    apply widthCastLabel_eq_of_val
    exact congrArg Fin.val hsource
  have htailCast :
      widthCastLabel htail
          (prodEquiv
            (pipelineTailEncoding.encode tail.1,
              GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.encode
                tail.2)) =
        cleanTailLabel P := by
    unfold cleanTailLabel
    apply widthCastLabel_eq_of_val
    rfl
  rw [hfullCast]
  rw [widthCastLabel_prodEquiv_assoc htail hfull
    (BinaryLabelEncoding.bool.encode control)
    (pipelineTailEncoding.encode tail.1)
    (GenericPointAddition.ExceptionalCleanup.Layout.selectorEncoding.encode
      tail.2)]
  rw [htailCast]
  rfl

/-- A total clean-point transition.  Outside the active generic domain it
uses the identity branch; semantic theorems below assume those exceptional
active branches do not occur. -/
noncomputable def nextPoint
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (addend : AffinePoint E)
    (control : Bool) (P : AffinePoint E) : AffinePoint E := by
  classical
  exact if hcontrol : control = true then
    if hsame : P = addend then P
    else if hinverse : P = AffinePoint.negate addend then P
    else ControlledPointAddition.controlledResultPoint
      E addend true P hsame hinverse
  else P

/-- One canonical ECADD body has its clean controlled basis action whenever
the active branch lies in the generic affine domain. -/
theorem controlTailProgram_clean_ket
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (addend : AffinePoint E)
    (control : Bool) (P : AffinePoint E)
    (hSame : control = true → P ≠ addend)
    (hInverse : control = true → P ≠ AffinePoint.negate addend) :
    (controlTailProgram E addend).applyNormalized
        (NormalizedVector.ket (rawCleanLabel control P)) =
      NormalizedVector.ket
        (rawCleanLabel control (nextPoint E addend control P)) := by
  cases control with
  | false =>
      have action := ControlledPointAddition.program_clean_ket_of_control_false
        E addend P
      have transported := widthCastProgram_applyNormalized_ket_of_eq
        rawEncoding_width_eq_one_add_tailWidth
        (ControlledPointAddition.program E addend)
        (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary false P))
        (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary false P)) action
      rw [cast_rawEncoding_encode_cleanBoundary] at transported
      have hnext : nextPoint E addend false P = P := by
        unfold nextPoint
        rw [dif_neg (by decide)]
      rw [hnext]
      unfold controlTailProgram
      exact transported
  | true =>
      have hsame := hSame rfl
      have hinverse := hInverse rfl
      have action := ControlledPointAddition.program_clean_ket
        E addend true P hsame hinverse
      have transported := widthCastProgram_applyNormalized_ket_of_eq
        rawEncoding_width_eq_one_add_tailWidth
        (ControlledPointAddition.program E addend)
        (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary true P))
        (GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.encode
          (ControlledPointAddition.cleanBoundary true
            (ControlledPointAddition.controlledResultPoint
              E addend true P hsame hinverse))) action
      rw [cast_rawEncoding_encode_cleanBoundary] at transported
      rw [cast_rawEncoding_encode_cleanBoundary
        (control := true)
        (P := ControlledPointAddition.controlledResultPoint
          E addend true P hsame hinverse)] at transported
      have hnext :
          nextPoint E addend true P =
            ControlledPointAddition.controlledResultPoint
              E addend true P hsame hinverse := by
        unfold nextPoint
        rw [dif_pos rfl, dif_neg hsame, dif_neg hinverse]
      rw [hnext]
      unfold controlTailProgram
      exact transported

/-- The canonical ECADD body stays inside its one-control-plus-tail carrier. -/
theorem controlTailProgram_physical_idx_subset_range
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (addend : AffinePoint E) :
    (controlTailProgram E addend).physical_idx ⊆
      List.range (1 + tailWidth) := by
  rw [controlTailProgram, widthCastProgram_physical_idx]
  have h :=
    GenericPointAddition.ExceptionalCleanup.translationProgram_physical_idx_subset_range
      (E := E) (Q := addend)
  have hwidth :
      Arithmetic.ModularInversion.physicalWidthFor params.width +
          20 * params.width + 13 =
        1 + tailWidth :=
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding_width_exact.symm.trans
      rawEncoding_width_eq_one_add_tailWidth
  rw [congrArg List.range hwidth] at h
  simpa only [ControlledPointAddition.program] using h

/-- Number of untouched exponent controls after position `i`. -/
def remainingControls (t : Nat) (i : Fin (2 * t)) : Nat :=
  2 * t - (i.val + 1)

omit params in
/-- The controls preceding, at, and following `i` occupy the whole exponent
register. -/
theorem controlWidth_eq (t : Nat) (i : Fin (2 * t)) :
    i.val + (1 + remainingControls t i) = 2 * t := by
  unfold remainingControls
  omega

/-- Pack the prefix, selected bit, and suffix around control wire `i` into the
flat exponent-register label. -/
def controlSlicesEquiv (t : Nat) (i : Fin (2 * t)) :
    (Fin (2 ^ i.val) ×
      (Fin 2 × Fin (2 ^ remainingControls t i))) ≃
        Fin (2 ^ (2 * t)) :=
  ((Equiv.prodCongr (Equiv.refl _)
      (prodEquiv (m := 1) (n := remainingControls t i))).trans
    (prodEquiv (m := i.val) (n := 1 + remainingControls t i))).trans
    (Equiv.cast
      (congrArg (fun width => Fin (2 ^ width)) (controlWidth_eq t i)))

/-- Prefix, selected bit, and suffix recovered around control wire `i`. -/
def controlSlices (t : Nat) (i : Fin (2 * t))
    (controls : Fin (2 ^ (2 * t))) :
    Fin (2 ^ i.val) ×
      (Fin 2 × Fin (2 ^ remainingControls t i)) :=
  (controlSlicesEquiv t i).symm controls

omit params in
@[simp] theorem controlSlicesEquiv_apply
    (t : Nat) (i : Fin (2 * t))
    (prefixLabel : Fin (2 ^ i.val)) (selected : Fin 2)
    (suffix : Fin (2 ^ remainingControls t i)) :
    controlSlicesEquiv t i (prefixLabel, selected, suffix) =
      widthCastLabel (controlWidth_eq t i)
        (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
          (prefixLabel,
            prodEquiv (m := 1) (n := remainingControls t i)
              (selected, suffix))) := by
  rfl

/-- Decode the complete one-bit basis-label type with the canonical Boolean
encoding. -/
def finTwoToBool (selected : Fin 2) : Bool :=
  if selected = 1 then true else false

omit params in
@[simp] theorem bool_encode_finTwoToBool (selected : Fin 2) :
    BinaryLabelEncoding.bool.encode (finTwoToBool selected) = selected := by
  fin_cases selected <;> rfl

omit params in
theorem finTwoToBool_eq_testBit_zero (selected : Fin 2) :
    finTwoToBool selected = selected.val.testBit 0 := by
  fin_cases selected <;> rfl

/-- Boolean value stored on exponent control wire `i`. -/
def cascadeControl (t : Nat) (controls : Fin (2 ^ (2 * t)))
    (i : Fin (2 * t)) : Bool :=
  finTwoToBool (controlSlices t i controls).2.1

omit params in
@[simp] theorem cascadeControl_encode
    (t : Nat) (controls : Fin (2 ^ (2 * t))) (i : Fin (2 * t)) :
    BinaryLabelEncoding.bool.encode (cascadeControl t controls i) =
      (controlSlices t i controls).2.1 := by
  exact bool_encode_finTwoToBool _

omit params in
/-- Repacking the recovered control slices returns the original exponent
label. -/
theorem controlSlices_repack
    (t : Nat) (controls : Fin (2 ^ (2 * t))) (i : Fin (2 * t)) :
    controlSlicesEquiv t i (controlSlices t i controls) = controls := by
  exact (controlSlicesEquiv t i).apply_symm_apply controls

omit params in
/-- The structural slice selected at `i` is exactly the bit stored on physical
wire `i` under the library's big-endian wire convention. -/
theorem cascadeControl_eq_testBit
    (t : Nat) (controls : Fin (2 ^ (2 * t))) (i : Fin (2 * t)) :
    cascadeControl t controls i =
      controls.val.testBit (WireAddress.bitIndex i).val := by
  let slices := controlSlices t i controls
  have hrepack : controlSlicesEquiv t i slices = controls := by
    exact controlSlices_repack t controls i
  have hcontrols :
      controls.val =
        (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
          (slices.1,
            prodEquiv (m := 1) (n := remainingControls t i)
              (slices.2.1, slices.2.2))).val := by
    calc
      controls.val = (controlSlicesEquiv t i slices).val :=
        congrArg Fin.val hrepack.symm
      _ = (widthCastLabel (controlWidth_eq t i)
          (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
            (slices.1,
              prodEquiv (m := 1) (n := remainingControls t i)
                (slices.2.1, slices.2.2)))).val := by
        exact congrArg Fin.val
          (controlSlicesEquiv_apply t i slices.1 slices.2.1 slices.2.2)
      _ = (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
          (slices.1,
            prodEquiv (m := 1) (n := remainingControls t i)
              (slices.2.1, slices.2.2))).val := by
        exact widthCastLabel_val _ _
  have hindex :
      (WireAddress.bitIndex i).val = remainingControls t i := by
    change 2 * t - 1 - i.val = 2 * t - (i.val + 1)
    rw [Nat.sub_sub]
    simp only [Nat.add_comm]
  rw [hcontrols, hindex]
  have houter := prodEquiv_testBit_right
    slices.1
    (prodEquiv (m := 1) (n := remainingControls t i)
      (slices.2.1, slices.2.2))
    (⟨remainingControls t i, by omega⟩ :
      Fin (1 + remainingControls t i))
  have hinner := prodEquiv_testBit_left
    (m := 1) (n := remainingControls t i)
    slices.2.1 slices.2.2 (⟨0, by omega⟩ : Fin 1)
  rw [houter]
  simpa only [cascadeControl, slices, Nat.add_zero,
    finTwoToBool_eq_testBit_zero] using hinner.symm

omit params in
/-- Flat `2 * t` control label obtained by packing two width-`t` exponent
registers in left/high then right/low order. -/
def pairedExponentLabel (t : Nat)
    (branch : Fin (2 ^ t) × Fin (2 ^ t)) : Fin (2 ^ (2 * t)) :=
  widthCastLabel (by omega : t + t = 2 * t) (prodEquiv branch)

omit params in
@[simp] theorem pairedExponentLabel_val (t : Nat)
    (branch : Fin (2 ^ t) × Fin (2 ^ t)) :
    (pairedExponentLabel t branch).val = (prodEquiv branch).val := by
  exact widthCastLabel_val _ _

omit params in
/-- Packing two fixed-width exponent labels is injective. -/
theorem pairedExponentLabel_injective (t : Nat) : Function.Injective
    (pairedExponentLabel t) := by
  intro left right equality
  apply prodEquiv.injective
  apply Fin.ext
  have values := congrArg Fin.val equality
  simpa only [pairedExponentLabel_val] using values

omit params in
/-- Packing two width-`t` labels places their controls in two consecutive
big-endian physical ranges. -/
theorem cascadeControl_prodEquiv (t : Nat)
    (branch : Fin (2 ^ t) × Fin (2 ^ t)) (i : Fin (2 * t)) :
    cascadeControl t (pairedExponentLabel t branch) i =
      ExceptionalOffsetAveraging.pairedBigEndianSelected t branch i := by
  rw [cascadeControl_eq_testBit]
  rw [pairedExponentLabel_val]
  unfold ExceptionalOffsetAveraging.pairedBigEndianSelected
  split_ifs with first
  · have localLt : t - 1 - i.val < t := by omega
    have bitIndexEquality :
        (WireAddress.bitIndex i).val = t + (t - 1 - i.val) := by
      change 2 * t - 1 - i.val = t + (t - 1 - i.val)
      omega
    rw [bitIndexEquality]
    exact prodEquiv_testBit_left branch.1 branch.2
      (⟨t - 1 - i.val, localLt⟩ : Fin t)
  · have localLt : t - 1 - (i.val - t) < t := by omega
    have bitIndexEquality :
        (WireAddress.bitIndex i).val = t - 1 - (i.val - t) := by
      change 2 * t - 1 - i.val = t - 1 - (i.val - t)
      omega
    rw [bitIndexEquality]
    exact prodEquiv_testBit_right branch.1 branch.2
      (⟨t - 1 - (i.val - t), localLt⟩ : Fin t)

/-- Global clean label for the exponent controls and shared ECADD tail. -/
def cleanLabel (t : Nat) (controls : Fin (2 ^ (2 * t)))
    (P : AffinePoint E) : Fin (2 ^ logicalQubitCount t) :=
  prodEquiv (controls, cleanTailLabel P)

/-- Global clean computational-basis state. -/
def cleanKet (t : Nat) (controls : Fin (2 ^ (2 * t)))
    (P : AffinePoint E) :
    NormalizedVector (Qubits (logicalQubitCount t)) :=
  NormalizedVector.ket (cleanLabel t controls P)

/-- Prefixing block `i` after inserting the later controls yields the common
shared-tail carrier width.  Keeping this arithmetic certificate opaque avoids
re-normalizing its proof whenever the placed circuit is unfolded. -/
theorem blockWidth_eq (t : Nat) (i : Fin (2 * t)) :
    i.val + (1 + remainingControls t i + tailWidth) =
      logicalQubitCount t := by
  unfold remainingControls logicalQubitCount
  omega

/-- Total clean-point update selected by the exponent bit used at block `i`. -/
noncomputable def blockPointStep
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t))) (i : Fin (2 * t))
    (addend P : AffinePoint E) : AffinePoint E :=
  nextPoint E addend (cascadeControl t controls i) P

/-- Clean basis label in the local prefix/control/suffix/tail association seen
before the final width transport of block `i`. -/
def blockInputCleanLabel
    (t : Nat) (i : Fin (2 * t))
    (controls : Fin (2 ^ (2 * t))) (P : AffinePoint E) :
    Fin (2 ^ (i.val + (1 + remainingControls t i + tailWidth))) :=
  prodEquiv (m := i.val)
    (n := 1 + remainingControls t i + tailWidth)
    ((controlSlices t i controls).1,
      prodEquiv (m := 1 + remainingControls t i) (n := tailWidth)
        (prodEquiv (m := 1) (n := remainingControls t i)
          (BinaryLabelEncoding.bool.encode
              (cascadeControl t controls i),
            (controlSlices t i controls).2.2),
          cleanTailLabel P))

/-- The block-local clean association and the global controls/tail association
denote the same flat computational-basis label. -/
theorem blockInputCleanLabel_cast_eq_cleanLabel
    (t : Nat) (i : Fin (2 * t))
    (controls : Fin (2 ^ (2 * t))) (P : AffinePoint E) :
    widthCastLabel (blockWidth_eq t i)
        (blockInputCleanLabel t i controls P) =
      cleanLabel t controls P := by
  let slices := controlSlices t i controls
  have hrepack : controlSlicesEquiv t i slices = controls := by
    exact controlSlices_repack t controls i
  have hcontrols :
      controls.val =
        (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
          (slices.1,
            prodEquiv (m := 1) (n := remainingControls t i)
              (slices.2.1, slices.2.2))).val := by
    calc
      controls.val = (controlSlicesEquiv t i slices).val :=
        congrArg Fin.val hrepack.symm
      _ = (widthCastLabel (controlWidth_eq t i)
          (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
            (slices.1,
              prodEquiv (m := 1) (n := remainingControls t i)
                (slices.2.1, slices.2.2)))).val := by
        exact congrArg Fin.val
          (controlSlicesEquiv_apply t i slices.1 slices.2.1 slices.2.2)
      _ = (prodEquiv (m := i.val) (n := 1 + remainingControls t i)
          (slices.1,
            prodEquiv (m := 1) (n := remainingControls t i)
              (slices.2.1, slices.2.2))).val := by
        exact widthCastLabel_val _ _
  have hcontrolsFlat :
      controls.val =
        slices.2.2.val +
          2 ^ remainingControls t i * slices.2.1.val +
          2 ^ (1 + remainingControls t i) * slices.1.val := by
    rw [hcontrols]
    simp [prodEquiv]
  apply Fin.ext
  rw [widthCastLabel_val]
  dsimp only [blockInputCleanLabel, cleanLabel]
  rw [cascadeControl_encode]
  change
    (cleanTailLabel P).val +
          2 ^ tailWidth *
            (slices.2.2.val +
              2 ^ remainingControls t i * slices.2.1.val) +
        2 ^ (1 + remainingControls t i + tailWidth) * slices.1.val =
      (cleanTailLabel P).val + 2 ^ tailWidth * controls.val
  rw [hcontrolsFlat, pow_add]
  ring

/-- Place one ECADD body on exponent control `i` and the shared tail.

`insertMiddle` moves the original tail past all controls following `i`, and
`prodRight` prefixes all controls preceding `i`.  Consequently control wire
zero of the body lands at `i`, while every body wire `j + 1` lands at the
shared global wire `2 * t + j`. -/
def blockAt
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) :
    UnitaryCircuit (Qubits (logicalQubitCount t)) :=
  widthCastProgram (blockWidth_eq t i)
    (UnitaryCircuit.prodRight (m := i.val)
      (UnitaryCircuit.insertMiddle
        (leftWidth := 1) (middleWidth := remainingControls t i)
        (rightWidth := tailWidth) (controlTailProgram E addend)))

/-- One placed block updates the shared clean point according to its selected
exponent bit.  Generic-domain assumptions are required only when that bit is
active. -/
theorem blockAt_applyNormalized_cleanKet
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) (controls : Fin (2 ^ (2 * t)))
    (P : AffinePoint E)
    (hactive : cascadeControl t controls i = true →
      P ≠ addend ∧ P ≠ AffinePoint.negate addend) :
    (blockAt E t i addend).applyNormalized (cleanKet t controls P) =
      cleanKet t controls (blockPointStep E t controls i addend P) := by
  have hbody := controlTailProgram_clean_ket E addend
    (cascadeControl t controls i) P
    (fun hcontrol => (hactive hcontrol).1)
    (fun hcontrol => (hactive hcontrol).2)
  have hbodyRaw :
      (controlTailProgram E addend).applyNormalized
          (NormalizedVector.ket
            (prodEquiv
              (BinaryLabelEncoding.bool.encode (cascadeControl t controls i),
                cleanTailLabel P))) =
        NormalizedVector.ket
          (prodEquiv
            (BinaryLabelEncoding.bool.encode (cascadeControl t controls i),
              cleanTailLabel (blockPointStep E t controls i addend P))) := by
    unfold rawCleanLabel at hbody
    unfold blockPointStep
    exact hbody
  have hinserted :=
    UnitaryCircuit.Realizes.insertMiddle_applyNormalized_ket_of_eq
      (controlTailProgram E addend)
      (BinaryLabelEncoding.bool.encode (cascadeControl t controls i))
      (controlSlices t i controls).2.2
      (cleanTailLabel P)
      (cleanTailLabel (blockPointStep E t controls i addend P))
      hbodyRaw
  have hprefixed :=
    UnitaryCircuit.Realizes.prodRight_applyNormalized_ket_of_eq
      (UnitaryCircuit.insertMiddle
        (leftWidth := 1) (middleWidth := remainingControls t i)
        (rightWidth := tailWidth) (controlTailProgram E addend))
      (controlSlices t i controls).1
      (prodEquiv
        (prodEquiv
          (BinaryLabelEncoding.bool.encode (cascadeControl t controls i),
            (controlSlices t i controls).2.2),
          cleanTailLabel P))
      (prodEquiv
        (prodEquiv
          (BinaryLabelEncoding.bool.encode (cascadeControl t controls i),
            (controlSlices t i controls).2.2),
          cleanTailLabel (blockPointStep E t controls i addend P)))
      hinserted
  have hprefixedClean :
      (UnitaryCircuit.prodRight (m := i.val)
        (UnitaryCircuit.insertMiddle
          (leftWidth := 1) (middleWidth := remainingControls t i)
          (rightWidth := tailWidth)
          (controlTailProgram E addend))).applyNormalized
          (NormalizedVector.ket
            (blockInputCleanLabel t i controls P)) =
        NormalizedVector.ket
          (blockInputCleanLabel t i controls
            (blockPointStep E t controls i addend P)) := by
    simpa only [blockInputCleanLabel] using hprefixed
  have hcast := widthCastProgram_applyNormalized_ket_of_eq
    (blockWidth_eq t i)
    (UnitaryCircuit.prodRight (m := i.val)
      (UnitaryCircuit.insertMiddle
        (leftWidth := 1) (middleWidth := remainingControls t i)
        (rightWidth := tailWidth) (controlTailProgram E addend)))
    (blockInputCleanLabel t i controls P)
    (blockInputCleanLabel t i controls
      (blockPointStep E t controls i addend P)) hprefixedClean
  rw [blockInputCleanLabel_cast_eq_cleanLabel] at hcast
  rw [blockInputCleanLabel_cast_eq_cleanLabel
    (P := blockPointStep E t controls i addend P)] at hcast
  unfold blockAt cleanKet
  exact hcast

@[simp] theorem blockAt_eventCost
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) :
    (blockAt E t i addend).eventCost =
      (ControlledPointAddition.program E addend).eventCost := by
  simp [blockAt, controlTailProgram]

@[simp] theorem blockAt_evaluatedEventDepth
    (assign : Resource.Event .quantum → Nat)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) :
    (blockAt E t i addend).evaluatedEventDepth assign =
      (ControlledPointAddition.program E addend).evaluatedEventDepth assign := by
  simp [blockAt, controlTailProgram]

/-- Width transport changes only the logical basis index, so a placed block
retains the footprint of the prefixed, middle-inserted ECADD body. -/
@[simp] theorem blockAt_physical_idx
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) :
    (blockAt E t i addend).physical_idx =
      (UnitaryCircuit.prodRight (m := i.val)
        (UnitaryCircuit.insertMiddle
          (leftWidth := 1) (middleWidth := remainingControls t i)
          (rightWidth := tailWidth)
          (controlTailProgram E addend))).physical_idx := by
  rfl

/-- Every placed block stays inside the complete exponent-plus-tail carrier. -/
theorem blockAt_physical_idx_subset_range
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat) (i : Fin (2 * t))
    (addend : AffinePoint E) :
    (blockAt E t i addend).physical_idx ⊆
      List.range (logicalQubitCount t) := by
  have bodyContained :
      (controlTailProgram E addend).physical_idx ⊆
        List.range (1 + tailWidth) := by
    exact controlTailProgram_physical_idx_subset_range E addend
  have insertedContained :
      (UnitaryCircuit.insertMiddle
        (leftWidth := 1) (middleWidth := remainingControls t i)
        (rightWidth := tailWidth) (controlTailProgram E addend)).physical_idx ⊆
        List.range (1 + remainingControls t i + tailWidth) :=
    UnitaryCircuit.insertMiddle_physical_idx_subset_range
      (controlTailProgram E addend) bodyContained
  have prefixedContained := UnitaryCircuit.prodRight_physical_idx_subset_range
    (m := i.val)
    (UnitaryCircuit.insertMiddle
      (leftWidth := 1) (middleWidth := remainingControls t i)
      (rightWidth := tailWidth) (controlTailProgram E addend))
    insertedContained
  intro index hindex
  rw [blockAt_physical_idx] at hindex
  have indexLtSource :
      index < i.val + (1 + remainingControls t i + tailWidth) :=
    List.mem_range.mp (prefixedContained hindex)
  exact List.mem_range.mpr (by
    rw [blockWidth_eq] at indexLtSource
    exact indexLtSource)

/-- Clean point after the first `processed` blocks in increasing control-wire
order. -/
noncomputable def pointPrefix
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) (processed : Nat) : AffinePoint E :=
  ((List.finRange (2 * t)).take processed).foldl
    (fun point i => blockPointStep E t controls i (addend i) point)
    initial

/-- Actual clean state after the first `processed` placed blocks. -/
noncomputable def statePrefix
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) (processed : Nat) :
    NormalizedVector (Qubits (logicalQubitCount t)) :=
  ((List.finRange (2 * t)).take processed).foldl
    (fun state i => (blockAt E t i (addend i)).applyNormalized state)
    (cleanKet t controls initial)

/-- The complete increasing-order clean point trajectory. -/
noncomputable def pointTrajectory
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) : AffinePoint E :=
  pointPrefix E t controls addend initial (2 * t)

/-- The complete increasing-order actual state trajectory. -/
noncomputable def stateTrajectory
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) :
    NormalizedVector (Qubits (logicalQubitCount t)) :=
  statePrefix E t controls addend initial (2 * t)

/-- Every actually selected branch meets the generic affine domain at the
point reached immediately before that block. -/
def ActiveBranchAdmissible
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) : Prop :=
  ∀ i : Fin (2 * t), cascadeControl t controls i = true →
    pointPrefix E t controls addend initial i.val ≠ addend i ∧
      pointPrefix E t controls addend initial i.val ≠
        AffinePoint.negate (addend i)

/-- Mathematical group multiplier accumulated before the first `processed`
cascade blocks. -/
def groupPrefixMultiplier
    (t : Nat) (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E) (processed : Nat) :
    GroupPoint E :=
  ExceptionalOffsetAveraging.prefixMultiplier (2 * t)
    (cascadeControl t) (fun i => (addend i).toGroupPoint)
    controls processed

/-- When the two exponent registers are packed consecutively and the affine
addends represent their canonical power schedule, the complete actual cascade
multiplier is exactly `leftBase^a * (rightBase^b)⁻¹`. -/
theorem groupPrefixMultiplier_prodEquiv_pairedBigEndian
    (t : Nat) (leftBase rightBase : GroupPoint E)
    (branch : Fin (2 ^ t) × Fin (2 ^ t))
    (addend : Fin (2 * t) → AffinePoint E)
    (haddend : ∀ i,
      (addend i).toGroupPoint =
        ExceptionalOffsetAveraging.pairedBigEndianAddend
          t leftBase rightBase i) :
    groupPrefixMultiplier t (pairedExponentLabel t branch) addend (2 * t) =
      leftBase ^ branch.1.val * (rightBase ^ branch.2.val)⁻¹ := by
  simpa only [groupPrefixMultiplier,
    ExceptionalOffsetAveraging.prefixMultiplier,
    cascadeControl_prodEquiv, haddend] using
      (ExceptionalOffsetAveraging.prefixMultiplier_pairedBigEndian
        (G := GroupPoint E) t leftBase rightBase branch)

/-- Group-level exceptional-domain predicate for one initial accumulator
offset and one exponent branch. -/
def GroupOffsetAdmissible
    (t : Nat) (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E) (offset : GroupPoint E) : Prop :=
  ExceptionalOffsetAveraging.Admissible (2 * t)
    (cascadeControl t) (fun i => (addend i).toGroupPoint)
    offset controls

/-- Affine negation agrees with inversion in the multiplicative group-point
wrapper. -/
theorem negate_toGroupPoint (point : AffinePoint E) :
    (AffinePoint.negate point).toGroupPoint = point.toGroupPoint⁻¹ := by
  exact congrArg
    (fun value : E.MathlibPoint => (⟨value⟩ : GroupPoint E))
    (AffinePoint.negate_toMathlib point)

omit params in
private theorem cascadeFinRange_take_succ {count : Nat}
    (i : Fin count) :
    (List.finRange count).take (i.val + 1) =
      (List.finRange count).take i.val ++ [i] := by
  have hindex : i.val < (List.finRange count).length := by
    simpa only [List.length_finRange] using i.isLt
  have hat : (List.finRange count)[i.val]'hindex = i := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [hat] using
    (List.take_concat_get' (List.finRange count) i.val hindex).symm

private theorem pointPrefix_succ
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) (processed : Nat)
    (hprocessed : processed < 2 * t) :
    pointPrefix E t controls addend initial (processed + 1) =
      blockPointStep E t controls ⟨processed, hprocessed⟩
        (addend ⟨processed, hprocessed⟩)
        (pointPrefix E t controls addend initial processed) := by
  unfold pointPrefix
  rw [cascadeFinRange_take_succ ⟨processed, hprocessed⟩,
    List.foldl_append]
  rfl

/-- A group-admissible initial offset makes every affine prefix denote the
corresponding product of the offset and selected scheduled addends. -/
theorem pointPrefix_toGroupPoint_of_groupOffsetAdmissible
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E)
    (hadmissible :
      GroupOffsetAdmissible t controls addend initial.toGroupPoint) :
    ∀ processed : Nat, processed ≤ 2 * t →
      (pointPrefix E t controls addend initial processed).toGroupPoint =
        initial.toGroupPoint *
          groupPrefixMultiplier t controls addend processed := by
  intro processed hprocessed
  induction processed with
  | zero =>
      simp [pointPrefix, groupPrefixMultiplier,
        ExceptionalOffsetAveraging.prefixMultiplier]
  | succ processed induction =>
      have processedLt : processed < 2 * t := Nat.lt_of_succ_le hprocessed
      let step : Fin (2 * t) := ⟨processed, processedLt⟩
      have prefixSpec := induction (Nat.le_of_lt processedLt)
      have prefixSpec' :
          (pointPrefix E t controls addend initial processed).toGroupPoint =
            initial.toGroupPoint *
              ExceptionalOffsetAveraging.prefixMultiplier (2 * t)
                (cascadeControl t) (fun i => (addend i).toGroupPoint)
                controls processed := by
        simpa only [groupPrefixMultiplier] using prefixSpec
      rw [pointPrefix_succ E t controls addend initial processed processedLt]
      unfold groupPrefixMultiplier
      rw [ExceptionalOffsetAveraging.prefixMultiplier_succ
        (G := GroupPoint E) (Branch := Fin (2 ^ (2 * t)))
        (2 * t) (cascadeControl t)
        (fun i => (addend i).toGroupPoint) controls processed processedLt]
      by_cases active : cascadeControl t controls step = true
      · have good := hadmissible step active
        have same :
            pointPrefix E t controls addend initial processed ≠ addend step := by
          intro equality
          apply good.1
          rw [← prefixSpec', equality]
        have inverse :
            pointPrefix E t controls addend initial processed ≠
              AffinePoint.negate (addend step) := by
          intro equality
          apply good.2
          rw [← prefixSpec', equality, negate_toGroupPoint]
        have resultLaw :
            (ControlledPointAddition.controlledResultPoint E (addend step) true
                (pointPrefix E t controls addend initial processed)
                same inverse).toGroupPoint =
              (pointPrefix E t controls addend initial processed).toGroupPoint *
                (addend step).toGroupPoint := by
          exact congrArg
            (fun value : E.MathlibPoint => (⟨value⟩ : GroupPoint E))
            (by
              simpa [groupPointEquiv, AffinePoint.toGroupPoint] using
                (ControlledPointAddition.controlledResultPoint_group_law
                  E (addend step) true
                  (pointPrefix E t controls addend initial processed)
                  same inverse))
        rw [if_pos active]
        unfold blockPointStep nextPoint
        rw [dif_pos active, dif_neg same, dif_neg inverse]
        calc
          _ =
              (pointPrefix E t controls addend initial processed).toGroupPoint *
                (addend step).toGroupPoint := resultLaw
          _ =
              (initial.toGroupPoint *
                  ExceptionalOffsetAveraging.prefixMultiplier (2 * t)
                    (cascadeControl t) (fun i => (addend i).toGroupPoint)
                    controls processed) *
                (addend step).toGroupPoint := by rw [prefixSpec']
          _ = initial.toGroupPoint *
              (ExceptionalOffsetAveraging.prefixMultiplier (2 * t)
                  (cascadeControl t) (fun i => (addend i).toGroupPoint)
                  controls processed *
                (addend step).toGroupPoint) := by rw [mul_assoc]
      · rw [if_neg active]
        unfold blockPointStep nextPoint
        rw [dif_neg active]
        exact prefixSpec'

/-- The group-level predicate implies the exact active-branch affine-domain
predicate consumed by the literal cascade semantics. -/
theorem activeBranchAdmissible_of_groupOffsetAdmissible
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E)
    (hadmissible :
      GroupOffsetAdmissible t controls addend initial.toGroupPoint) :
    ActiveBranchAdmissible E t controls addend initial := by
  intro step active
  have prefixSpec := pointPrefix_toGroupPoint_of_groupOffsetAdmissible
    E t controls addend initial hadmissible step.val (Nat.le_of_lt step.isLt)
  simp only [groupPrefixMultiplier] at prefixSpec
  have good := hadmissible step active
  constructor
  · intro equality
    apply good.1
    rw [← prefixSpec, equality]
  · intro equality
    apply good.2
    rw [← prefixSpec, equality, negate_toGroupPoint]

/-- The complete admissible point trajectory denotes the fixed offset times
the complete selected group multiplier. -/
theorem pointTrajectory_toGroupPoint_of_groupOffsetAdmissible
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E)
    (hadmissible :
      GroupOffsetAdmissible t controls addend initial.toGroupPoint) :
    (pointTrajectory E t controls addend initial).toGroupPoint =
      initial.toGroupPoint *
        groupPrefixMultiplier t controls addend (2 * t) := by
  unfold pointTrajectory
  exact pointPrefix_toGroupPoint_of_groupOffsetAdmissible
    E t controls addend initial hadmissible (2 * t) (Nat.le_refl _)

private theorem statePrefix_succ
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E) (processed : Nat)
    (hprocessed : processed < 2 * t) :
    statePrefix E t controls addend initial (processed + 1) =
      (blockAt E t ⟨processed, hprocessed⟩
        (addend ⟨processed, hprocessed⟩)).applyNormalized
        (statePrefix E t controls addend initial processed) := by
  unfold statePrefix
  rw [cascadeFinRange_take_succ ⟨processed, hprocessed⟩,
    List.foldl_append]
  rfl

/-- Every admissible prefix of the actual circuit trajectory remains the
clean ket of the corresponding point trajectory. -/
theorem statePrefix_cleanKet
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (controls : Fin (2 ^ (2 * t)))
    (addend : Fin (2 * t) → AffinePoint E)
    (initial : AffinePoint E)
    (hactive : ActiveBranchAdmissible E t controls addend initial) :
    ∀ processed : Nat, processed ≤ 2 * t →
      statePrefix E t controls addend initial processed =
        cleanKet t controls
          (pointPrefix E t controls addend initial processed) := by
  intro processed hprocessed
  induction processed with
  | zero => rfl
  | succ processed ih =>
      have hlt : processed < 2 * t := Nat.lt_of_succ_le hprocessed
      let i : Fin (2 * t) := ⟨processed, hlt⟩
      have hinduction := ih (Nat.le_of_lt hlt)
      have hblock := blockAt_applyNormalized_cleanKet
        E t i (addend i) controls
        (pointPrefix E t controls addend initial processed)
        (fun hcontrol => hactive i hcontrol)
      calc
        statePrefix E t controls addend initial (processed + 1) =
            (blockAt E t i (addend i)).applyNormalized
              (statePrefix E t controls addend initial processed) := by
          simpa only [i] using
            statePrefix_succ E t controls addend initial processed hlt
        _ = (blockAt E t i (addend i)).applyNormalized
              (cleanKet t controls
                (pointPrefix E t controls addend initial processed)) :=
          congrArg (fun state =>
            (blockAt E t i (addend i)).applyNormalized state) hinduction
        _ = cleanKet t controls
              (blockPointStep E t controls i (addend i)
                (pointPrefix E t controls addend initial processed)) := hblock
        _ = cleanKet t controls
              (pointPrefix E t controls addend initial (processed + 1)) := by
          exact congrArg (cleanKet t controls)
            (pointPrefix_succ E t controls addend initial processed hlt).symm

/-- The resource-bearing distinct-control cascade before adding a zero-cost
full-carrier footprint witness. -/
def coreProgram
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    UnitaryCircuit (Qubits (logicalQubitCount t)) :=
  UnitaryCircuit.indexedProductNamed "ecadd-distinct-controls" (2 * t)
    (UnitaryCircuit.identity (Qubits (logicalQubitCount t))
      [] List.nodup_nil)
    (fun i => blockAt E t i (addend i))

/-- The core circuit action is exactly its explicit increasing-order state
trajectory, without any generic-domain assumption. -/
theorem coreProgram_applyNormalized_eq_stateTrajectory
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E)
    (controls : Fin (2 ^ (2 * t))) (initial : AffinePoint E) :
    (coreProgram E t addend).applyNormalized
        (cleanKet t controls initial) =
      stateTrajectory E t controls addend initial := by
  rw [coreProgram, UnitaryCircuit.applyNormalized_indexedProductNamed,
    UnitaryCircuit.applyNormalized_identity]
  unfold stateTrajectory statePrefix
  have htake :
      (List.finRange (2 * t)).take (2 * t) =
        List.finRange (2 * t) := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange (2 * t)))
  rw [htake]
  simp only [List.ofFn_eq_map, List.foldl_map]

/-- The complete actual trajectory is the clean ket of the complete point
trajectory on every admissible active path. -/
theorem stateTrajectory_cleanKet
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E)
    (controls : Fin (2 ^ (2 * t))) (initial : AffinePoint E)
    (hactive : ActiveBranchAdmissible E t controls addend initial) :
    stateTrajectory E t controls addend initial =
      cleanKet t controls
        (pointTrajectory E t controls addend initial) := by
  unfold stateTrajectory pointTrajectory
  exact statePrefix_cleanKet E t controls addend initial hactive
    (2 * t) (Nat.le_refl _)

/-- Clean basis action of the resource-bearing cascade on every admissible
active path. -/
theorem coreProgram_applyNormalized_cleanKet
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E)
    (controls : Fin (2 ^ (2 * t))) (initial : AffinePoint E)
    (hactive : ActiveBranchAdmissible E t controls addend initial) :
    (coreProgram E t addend).applyNormalized
        (cleanKet t controls initial) =
      cleanKet t controls
        (pointTrajectory E t controls addend initial) := by
  rw [coreProgram_applyNormalized_eq_stateTrajectory,
    stateTrajectory_cleanKet E t addend controls initial hactive]

/-- The literal distinct-control cascade on one shared ECADD tail.  The final
identity has a full physical footprint but no operator, event, or depth cost;
it records the complete interface required by concrete circuit access. -/
def program
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    UnitaryCircuit (Qubits (logicalQubitCount t)) :=
  UnitaryCircuit.seq (coreProgram E t addend)
    (UnitaryCircuit.identity (Qubits (logicalQubitCount t))
      (List.range (logicalQubitCount t)) List.nodup_range)

/-- The full-footprint cascade has the same clean basis action as its
resource-bearing core. -/
theorem program_applyNormalized_cleanKet
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E)
    (controls : Fin (2 ^ (2 * t))) (initial : AffinePoint E)
    (hactive : ActiveBranchAdmissible E t controls addend initial) :
    (program E t addend).applyNormalized
        (cleanKet t controls initial) =
      cleanKet t controls
        (pointTrajectory E t controls addend initial) := by
  rw [program, UnitaryCircuit.applyNormalized_seq,
    coreProgram_applyNormalized_cleanKet E t addend controls initial hactive,
    UnitaryCircuit.applyNormalized_identity]

/-- The full-range identity start makes the cascade footprint exactly the
complete carrier while contributing no event or depth cost. -/
theorem program_physical_idx_eq_range
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    (program E t addend).physical_idx =
      List.range (logicalQubitCount t) := by
  unfold program UnitaryCircuit.seq
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  unfold coreProgram UnitaryCircuit.indexedProductNamed
  apply UnitaryCircuit.foldl_unionPhysicalIdx_subset
  · intro index member
    cases member
  · intro footprint member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact blockAt_physical_idx_subset_range E t i (addend i)

/-- Sequential depth of the resource-bearing cascade is the sum of its
literal block depths. -/
@[simp] theorem coreProgram_evaluatedEventDepth
    (assign : Resource.Event .quantum → Nat)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    (coreProgram E t addend).evaluatedEventDepth assign =
      ∑ i, (blockAt E t i (addend i)).evaluatedEventDepth assign := by
  rw [coreProgram, UnitaryCircuit.evaluatedEventDepth_indexedProductNamed]
  simp [UnitaryCircuit.evaluatedEventDepth]

/-- The full-footprint identity contributes no evaluated depth. -/
@[simp] theorem program_evaluatedEventDepth
    (assign : Resource.Event .quantum → Nat)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    (program E t addend).evaluatedEventDepth assign =
      ∑ i, (blockAt E t i (addend i)).evaluatedEventDepth assign := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq,
    coreProgram_evaluatedEventDepth]
  simp [UnitaryCircuit.evaluatedEventDepth]

omit params in
private theorem resourcePool_count_finset_sum
    {kind : ProblemKind} {Index : Type} [Fintype Index]
    (focus : Resource.Event kind) (pool : Index → ResourcePool kind) :
    ResourcePool.count focus (∑ index, pool index) =
      ∑ index, ResourcePool.count focus (pool index) := by
  classical
  have aux : ∀ indices : Finset Index,
      ResourcePool.count focus (∑ index ∈ indices, pool index) =
        ∑ index ∈ indices, ResourcePool.count focus (pool index) := by
    intro indices
    induction indices using Finset.induction with
    | empty => simp
    | @insert index rest hindex ih =>
        simp [Finset.sum_insert, hindex, ResourcePool.count_add, ih]
  simpa using aux Finset.univ

/-- Same-circuit Toffoli bound: one width-only ECADD bound for each of the
`2 * t` actual placed blocks. -/
theorem program_toffoli_count_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (program E t addend).eventCost ≤
      (2 * t) * ControlledPointAddition.toffoliCountBound params.width := by
  simp only [program, coreProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add, add_zero]
  rw [resourcePool_count_finset_sum]
  calc
    (∑ i : Fin (2 * t), ResourcePool.count (.gate (.builtin "toffoli"))
        (blockAt E t i (addend i)).eventCost) ≤
        ∑ _i : Fin (2 * t),
          ControlledPointAddition.toffoliCountBound params.width :=
      Finset.sum_le_sum fun i _ => by
        rw [blockAt_eventCost]
        exact ControlledPointAddition.program_toffoli_count_le E (addend i)
    _ = (2 * t) * ControlledPointAddition.toffoliCountBound params.width := by
      simp

/-- Same-circuit sequential unit-depth bound for the actual placed cascade. -/
theorem program_unitDepth_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E) :
    (program E t addend).evaluatedEventDepth (fun _ => 1) ≤
      (2 * t) * ControlledPointAddition.circuitDepthBound params.width := by
  rw [program_evaluatedEventDepth]
  calc
    (∑ i : Fin (2 * t),
        (blockAt E t i (addend i)).evaluatedEventDepth (fun _ => 1)) ≤
        ∑ _i : Fin (2 * t),
          ControlledPointAddition.circuitDepthBound params.width :=
      Finset.sum_le_sum fun i _ => by
        rw [blockAt_evaluatedEventDepth]
        exact ControlledPointAddition.program_unitDepth_le E (addend i)
    _ = (2 * t) * ControlledPointAddition.circuitDepthBound params.width := by
      simp

/-- The complete cascade contains no opaque quantum-subroutine event. -/
theorem program_quantumSubroutine_count_zero
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (t : Nat)
    (addend : Fin (2 * t) → AffinePoint E)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
        (program E t addend).eventCost = 0 := by
  simp only [program, coreProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.indexedProductNamed_eventCost, UnitaryCircuit.identity_eventCost,
    zero_add, add_zero]
  rw [resourcePool_count_finset_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [blockAt_eventCost]
  simpa only [ControlledPointAddition.program] using
    (GenericPointAddition.ExceptionalCleanup.translationProgram_quantumSubroutine_count_zero
      (E := E) (Q := addend i) label)

end

end ExponentControlledECADDCascade
end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
