/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Flag
import all QuantumAlg.Util.ThresholdStream.Boundary

/-!
# Signed overflow fused into the actual moving-flag callbacks

The ordinary moving-flag callback and the selected top instruction
share one actual unary traversal. The top word ignores the moving
flag, so its action follows the operand action while the same physical
flag is cleared. Inverting the pre-overflow traversal therefore puts
the top instruction before the descending operand chain, as required
by the original source [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA ArithmeticTemplate

/-- Each top source instruction shares exactly its original operand stage. -/
def stage : ArithmeticTop.Kind → Stage
  | .pre => .descendingXor
  | .carry => .carry

private def leaf (width : Nat) : EncodedBit (encoding width) :=
  (SelectionFrame.frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩

/-- The native boundary toggle and selected overflow gates use the same actual computed prefix. -/
def callback (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  ((family width (stage kind)).callback (QubitLayout.canonical _) .empty label).seq
    (ArithmeticTop.callback width kind label)

/-- Explicit Boolean visits retain the exact operand, boundary, and flag actions. -/
def callbackStep (width : Nat) (kind : ArithmeticTop.Kind) (index : Nat)
    (selected : Bool) (state : Data width) : Data width :=
  let next := (payload width (stage kind) index).callbackStep selected state
  if selected then GateSpec.stepList (ArithmeticTop.source width kind index) next else next

/-- The complete native callback realizes the explicit visit on arbitrary coherent source data. -/
lemma callback_realizes (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (callback width kind label) environment
      (fun state => callbackStep width kind label.val ((leaf width).get state) state) := by
  have first := (payload width (stage kind) label.val).callback_realizes (leaf width)
    ((family width (stage kind)).activeStack label _).symm
    ((family width (stage kind)).sourceStack label _) (QubitLayout.canonical _) .empty
    environment
  have second := (ArithmeticTop.payload width kind label).program_realizes
    (QubitLayout.canonical _) .empty environment
  have complete := UnitaryCircuit.Realizes.seq first second
  apply complete.congrStep
  intro state
  have retained := (payload width (stage kind) label.val).callbackStep_get (leaf width)
    ((family width (stage kind)).activeStack label _)
    ((family width (stage kind)).sourceStack label _) ((leaf width).get state) state
  change (if (leaf width).get ((payload width (stage kind) label.val).callbackStep
      ((leaf width).get state) state) then
      GateSpec.stepList (ArithmeticTop.source width kind label.val)
        ((payload width (stage kind) label.val).callbackStep ((leaf width).get state) state)
      else (payload width (stage kind) label.val).callbackStep ((leaf width).get state) state) = _
  rw [retained]
  rfl

private lemma operand_preserves (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) (selected : Bool) :
    (SelectionFrame.frame width).Preserves
      ((payload width (stage kind) label.val).callbackStep selected) :=
  (payload width (stage kind) label.val).callbackStep_preserves (SelectionFrame.frame width)
    ((family width (stage kind)).activeAddress label)
    ((family width (stage kind)).activeStack label)
    ((family width (stage kind)).sourceAddress label)
    ((family width (stage kind)).sourceStack label) selected

private lemma operand_independent (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) (selected : Bool) :
    (SelectionFrame.frame width).IndependentPrefixes
      ((payload width (stage kind) label.val).callbackStep selected) :=
  (payload width (stage kind) label.val).callbackStep_independent (SelectionFrame.frame width)
    (fun index => (family width (stage kind)).activeStack label index.succ)
    (fun index => (family width (stage kind)).sourceStack label index.succ) selected

/-- Every explicit visit retains all original address, Ctrl and prefix coordinates. -/
lemma callbackStep_preserves (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) (selected : Bool) :
    (SelectionFrame.frame width).Preserves (callbackStep width kind label.val selected) := by
  cases selected with
  | false => exact operand_preserves width kind label false
  | true =>
      constructor
      · intro index state
        exact ((ArithmeticTop.payload width kind label).action_preserves.1 index _).trans
          ((operand_preserves width kind label true).1 index state)
      · intro index state
        exact ((ArithmeticTop.payload width kind label).action_preserves.2 index _).trans
          ((operand_preserves width kind label true).2 index state)

/-- Fused callbacks never inspect unused computed-prefix values. -/
lemma callbackStep_independent (width : Nat) (kind : ArithmeticTop.Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) (selected : Bool) :
    (SelectionFrame.frame width).IndependentPrefixes
      (callbackStep width kind label.val selected) := by
  cases selected with
  | false => exact operand_independent width kind label false
  | true =>
      intro index state
      change (ArithmeticTop.payload width kind label).action
          ((payload width (stage kind) label.val).callbackStep true
            (((SelectionFrame.frame width).stack index.succ).flip state)) = _
      rw [operand_independent width kind label true index state]
      exact (ArithmeticTop.payload width kind label).action_independent index _

private lemma top_flag_disjoint (width : Nat) (kind : ArithmeticTop.Kind) (index : Nat)
    (gate : GateSpec (encoding width)) (present : gate ∈ ArithmeticTop.source width kind index) :
    GateSpec.bitDisjoint (conjunctionBit width) gate := by
  apply ArithmeticTemplate.below_disjoint gate
    (ArithmeticTop.source_below width kind index gate present)
  rw [conjunctionBit_wire, SharedEEA.iterationBit_wire, SharedEEA.encoding_width]
  omega

/-- The literal overflow word acts only on the retained base, independently of the moving flag. -/
def boundaryAction (width : Nat) (kind : ArithmeticTop.Kind) (index : Nat)
    (base : FlagBase width) : FlagBase width :=
  (flagEquiv width (GateSpec.stepList (ArithmeticTop.source width kind index)
    ((flagEquiv width).symm (base, false)))).1

private lemma top_flagEquiv (width : Nat) (kind : ArithmeticTop.Kind) (index : Nat)
    (base : FlagBase width) (active : Bool) :
    flagEquiv width (GateSpec.stepList (ArithmeticTop.source width kind index)
      ((flagEquiv width).symm (base, active))) =
      (boundaryAction width kind index base, active) := by
  have clean := GateSpec.stepList_get_of_bitDisjoint (ArithmeticTop.source width kind index)
    (conjunctionBit width) (top_flag_disjoint width kind index)
    ((flagEquiv width).symm (base, false))
  have zero : flagEquiv width (GateSpec.stepList (ArithmeticTop.source width kind index)
      ((flagEquiv width).symm (base, false))) =
      (boundaryAction width kind index base, false) := by
    apply Prod.ext
    · rfl
    · exact clean
  cases active with
  | false => exact zero
  | true =>
      have flipped : (flagEquiv width).symm (base, true) =
          (conjunctionBit width).flip ((flagEquiv width).symm (base, false)) := rfl
      rw [flipped, GateSpec.stepList_flip_comm_of_bitDisjoint _ _
        (top_flag_disjoint width kind index), flagEquiv_flip, zero]
      rfl

/-- The actual visit equals the source-order-preserving selected boundary recurrence. -/
lemma callback_threshold (width : Nat) (kind : ArithmeticTop.Kind) (index : Nat)
    (enabled : Bool) (last : Nat) (state : Data width) :
    flagEquiv width (callbackStep width kind index (enabled && decide (index = last)) state) =
      ThresholdStream.Boundary.forwardStep (baseAction width (stage kind))
        (boundaryAction width kind) enabled last (flagEquiv width state) index := by
  let selected := enabled && decide (index = last)
  have operand := ArithmeticTemplate.callback_threshold width (stage kind) index
    enabled last state
  have normalization : (payload width (stage kind) index).callbackStep selected state =
      (flagEquiv width).symm
        (ThresholdStream.forwardStep (baseAction width (stage kind)) enabled last
          (flagEquiv width state) index) :=
    ((flagEquiv width).symm_apply_apply _).symm.trans
      (congrArg (flagEquiv width).symm operand)
  change flagEquiv width (if selected then
    GateSpec.stepList (ArithmeticTop.source width kind index)
      ((payload width (stage kind) index).callbackStep selected state)
    else (payload width (stage kind) index).callbackStep selected state) = _
  rw [normalization]
  cases chosen : selected with
  | false =>
      simp only [Bool.false_eq_true, if_false, Equiv.apply_symm_apply]
      simp only [ThresholdStream.forwardStep, ThresholdStream.Boundary.forwardStep,
        show (enabled && decide (index = last)) = false from chosen,
        Bool.false_eq_true, if_false]
  | true =>
      simp only [if_true, ThresholdStream.forwardStep]
      rw [top_flagEquiv]
      simp only [ThresholdStream.Boundary.forwardStep,
        show (enabled && decide (index = last)) = true from chosen, if_true]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
