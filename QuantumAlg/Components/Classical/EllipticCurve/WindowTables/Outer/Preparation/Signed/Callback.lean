/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Preservation
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-! # Complete caller-Store postcondition of the actual signed-row callback -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalAlgorithms.EllipticCurve
open QuantumAlg.ClassicalRoutines.Modular.NativePower

noncomputable section
variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The four declared constant cells are outside all six table outputs. -/
lemma outputFree_constant (frame : Frame ctx width) (index : Fin 10)
    (lower : 4 ≤ index.val) (upper : index.val < 8)
    {shape : CShape} (observed : CInputRef ctx shape)
    (support : observed.storageKeys = [frame.keyAt index]) :
    OutputFree frame.coordinates observed := by
  have free (output : Fin 10) (outside : output.val < 4 ∨ 8 ≤ output.val) :
      frame.keyAt output ∉ observed.storageKeys := by
    rw [support, List.mem_singleton]
    exact frame.keyAt_ne output index (by
      intro same
      have values := congrArg Fin.val same
      omega)
  intro key member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact free 8 (by decide)
  · exact free 9 (by decide)
  · exact free 0 (by decide)
  · exact free 1 (by decide)
  · exact free 2 (by decide)
  · exact free 3 (by decide)

variable {model : ExecutionModel} [BitWord.Selected model]

attribute [local irreducible] callbackRecord callbackStore

/-- The actual callback preserves all constants from its post-initialization source Store. -/
lemma callback_constants {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (curve : CurveSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment) (source : Store outer)
    (before : Store inner × model.HiddenState) (reads : lift.ReadsAs source before.1)
    (constants : Constants frame curve source) :
    Constants (frame.transport lift) curve
      (callbackRecord frame curve.field base target cells distinct lift separated
        environment before).1.1 := by
  have stable {shape : CShape} (observed : CInputRef outer shape)
      (free : OutputFree frame.coordinates observed) :=
    (callbackRecord_read_other frame curve.field base target cells distinct lift
      separated environment before observed free).trans (reads observed)
  constructor
  · exact (stable (wordRead frame.modulus)
      (outputFree_constant frame 4 (by decide) (by decide) _ rfl)).trans constants.modulus
  · exact (congrArg CShape.Value.toNat (stable (.storage frame.zero.toCStorageRef)
      (outputFree_constant frame 5 (by decide) (by decide) _ rfl))).trans constants.zero
  · exact (congrArg CShape.Value.toNat (stable (.storage frame.one.toCStorageRef)
      (outputFree_constant frame 6 (by decide) (by decide) _ rfl))).trans constants.one
  · change (((callbackRecord frame curve.field base target cells distinct lift separated
      environment before).1.1.read (lift.liftInput (.storage frame.curveA.toCStorageRef))).toNat :
        ZMod curve.field.modulus) = curve.curve.a
    rw [stable (.storage frame.curveA.toCStorageRef)
      (outputFree_constant frame 7 (by decide) (by decide) _ rfl)]
    exact constants.curveA

/-- The two family values and constants refer to the actual caller Store after lexical release. -/
lemma callback_restricted_post {outer inner : RuntimeCtx model.kind}
    (frame : Frame outer width) (curve : CurveSpec width)
    (base target : CInputRef outer (PointShape width))
    (cells : Cells inner (scratchShapes width)) (distinct : cells.Distinct)
    (lift : Transport outer inner) (separated : cells.TransportSeparated lift)
    (environment : model.Environment) (source : Store outer)
    (before : Store inner × model.HiddenState) (reads : lift.ReadsAs source before.1)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (secondOrder : addOrderOf second.toMathlib = order)
    (baseRep : PointRepresents curve (source.read base) first.toMathlib)
    (targetRep : PointRepresents curve (source.read target) second.toMathlib)
    (constants : Constants frame curve source)
    (baseFree : OutputFree frame.coordinates base)
    (targetFree : OutputFree frame.coordinates target) :
    let returned := lift.restrict
      (callbackRecord frame curve.field base target cells distinct lift separated
        environment before).1.1
    Constants frame curve returned ∧ pairedRows curve frame first second returned ∧
      returned.read base = source.read base ∧ returned.read target = source.read target := by
  let actual := (callbackRecord frame curve.field base target cells distinct lift separated
    environment before).1.1
  have returnedReads : lift.ReadsAs (lift.restrict actual) actual :=
    lift.workspaceTransport_restrict_readsAs actual
  have constantsHere := callback_constants frame curve base target cells distinct lift separated
    environment source before reads constants
  have rowsHere := callback_rows_of_post_init_source frame curve base target cells distinct
    lift separated environment source before reads first second order prime large
    firstOrder secondOrder baseRep targetRep constants.modulus constants.curveA constants.zero
  rw [callbackStore_eq_callbackRecord] at rowsHere
  refine ⟨constants_of_readsAs frame curve lift _ actual returnedReads constantsHere,
    pairedRows_of_readsAs frame curve lift _ actual returnedReads first second rowsHere, ?_, ?_⟩
  · exact (returnedReads base).symm.trans
      ((callbackRecord_read_other frame curve.field base target cells distinct lift separated
        environment before base baseFree).trans (reads base))
  · exact (returnedReads target).symm.trans
      ((callbackRecord_read_other frame curve.field base target cells distinct lift separated
        environment before target targetFree).trans (reads target))

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed
