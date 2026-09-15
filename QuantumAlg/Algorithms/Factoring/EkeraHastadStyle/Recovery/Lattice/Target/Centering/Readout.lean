/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Target.Centering
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual centered-coordinate stores and arithmetic arms

The readout follows the real stored predicate values and actual arithmetic
updates. The zero and negative arms have exact unsigned residue equations
at every width, including zero. Each selected arm writes only the target;
the complete prefix additionally writes its scratch and two predicate cells.
Source initialization and layout separation are connected in later consumers.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual self-subtraction arm produces the unique zero word at every width. -/
theorem nativeLattice_targetCentering_zero_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (zeroOp refs)).read (.storage refs.output.toCStorageRef)).toNat = 0 := by
  have actual : ((store.applyOp (zeroOp refs)).read
      (.storage refs.output.toCStorageRef)).toNat =
      ((store.read refs.preimage).toNat + 2 ^ width - (store.read refs.preimage).toNat) %
        2 ^ width :=
    congrArg CShape.Value.toNat (Store.read_applyOp_output store (zeroOp refs))
  have cancel : (store.read refs.preimage).toNat + 2 ^ width -
      (store.read refs.preimage).toNat = 2 ^ width := by omega
  exact actual.trans (by rw [cancel, Nat.mod_self])

/-- Actual complement followed by increment gives the original modular negative preimage. -/
theorem nativeLattice_targetCentering_negate_read (refs : Refs ctx width) (store : Store ctx) :
    ((negateStore refs store).read (.storage refs.output.toCStorageRef)).toNat =
      (2 ^ width - (store.read refs.preimage).toNat) % 2 ^ width := by
  let complemented := store.applyOp (complementOp refs)
  have bounded := (store.read refs.preimage).toNat_lt
  have capacityPositive := Nat.two_pow_pos width
  have complementFits : 2 ^ width - 1 - (store.read refs.preimage).toNat < 2 ^ width := by
    omega
  have complementedValue : (complemented.read (.storage refs.output.toCStorageRef)).toNat =
      2 ^ width - 1 - (store.read refs.preimage).toNat := by
    have actual : (complemented.read (.storage refs.output.toCStorageRef)).toNat =
        (2 ^ width - 1 - (store.read refs.preimage).toNat) % 2 ^ width :=
      congrArg CShape.Value.toNat (Store.read_applyOp_output store (complementOp refs))
    exact actual.trans (Nat.mod_eq_of_lt complementFits)
  have incremented : ((negateStore refs store).read
      (.storage refs.output.toCStorageRef)).toNat =
      ((complemented.read (.storage refs.output.toCStorageRef)).toNat + 1) % 2 ^ width :=
    congrArg CShape.Value.toNat (Store.read_applyOp_output complemented (incrementOp refs))
  have cancellation : 2 ^ width - 1 - (store.read refs.preimage).toNat + 1 =
      2 ^ width - (store.read refs.preimage).toNat := by omega
  exact incremented.trans (by rw [complementedValue, cancellation])

/-- The remaining actual arm is exactly the source modulus-minus-preimage word subtraction. -/
theorem nativeLattice_targetCentering_subtract_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (subtractOp refs)).read (.storage refs.output.toCStorageRef)).toNat =
      ((store.read refs.modulus).toNat + 2 ^ width - (store.read refs.preimage).toNat) %
        2 ^ width :=
  congrArg CShape.Value.toNat (Store.read_applyOp_output store (subtractOp refs))

/-- The complete actual store follows the two predicate values read after all four prefix writes. -/
theorem nativeLattice_targetCentering_step_store (refs : Refs ctx width) (store : Store ctx) :
    (step refs store).1 =
      let selected := decisionStore refs store
      if (selected.read (.storage refs.isZero.toCStorageRef)).toBool then
        selected.applyOp (zeroOp refs)
      else if (selected.read (.storage refs.belowHalf.toCStorageRef)).toBool then
        negateStore refs selected
      else selected.applyOp (subtractOp refs) := by
  dsimp only [step, selectionStep]
  cases zeroValue : (decisionStore refs store).read (.storage refs.isZero.toCStorageRef) with
  | bit bit =>
      cases bit
      · dsimp only [zeroStep, nonzeroStep]
        cases belowValue :
            (decisionStore refs store).read (.storage refs.belowHalf.toCStorageRef) with
        | bit bit => cases bit <;> rfl
      · rfl

private theorem below_read_other (refs : Refs ctx width) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (free : refs.output.key ∉ other.storageKeys) (store : Store ctx) :
    (belowStep refs value store).1.read other = store.read other := by
  cases value with
  | bit bit =>
      cases bit
      · exact Store.read_applyOp_of_not_mem_storageKeys store (subtractOp refs) other free
      · exact (Store.read_applyOp_of_not_mem_storageKeys
          (store.applyOp (complementOp refs)) (incrementOp refs) other free).trans
          (Store.read_applyOp_of_not_mem_storageKeys store (complementOp refs) other free)

private theorem zero_read_other (refs : Refs ctx width) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (free : refs.output.key ∉ other.storageKeys) (store : Store ctx) :
    (zeroStep refs value store).1.read other = store.read other := by
  cases value with
  | bit bit =>
      cases bit
      · exact below_read_other refs (store.read (.storage refs.belowHalf.toCStorageRef))
          other free store
      · exact Store.read_applyOp_of_not_mem_storageKeys store (zeroOp refs) other free

/-- The actual selected arithmetic preserves every structural read outside the destination. -/
theorem nativeLattice_targetCentering_selection_read_other (refs : Refs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (free : refs.output.key ∉ other.storageKeys) (store : Store ctx) :
    (selectionStep refs store).1.read other = store.read other :=
  zero_read_other refs (store.read (.storage refs.isZero.toCStorageRef)) other free store

/-- The four original predicate instructions preserve all reads outside their actual three cells. -/
theorem nativeLattice_targetCentering_decision_read_other (refs : Refs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (zeroFree : refs.isZero.key ∉ other.storageKeys)
    (scratchFree : refs.scratch.key ∉ other.storageKeys)
    (belowFree : refs.belowHalf.key ∉ other.storageKeys) (store : Store ctx) :
    (decisionStore refs store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys
    (((store.applyOp (equalOp refs)).applyOp (copyOp refs)).applyOp (halfOp refs))
    (lessOp refs) other belowFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys
      ((store.applyOp (equalOp refs)).applyOp (copyOp refs)) (halfOp refs) other scratchFree).trans
      ((Store.read_applyOp_of_not_mem_storageKeys
        (store.applyOp (equalOp refs)) (copyOp refs) other scratchFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (equalOp refs) other zeroFree)))

/-- The whole real computation preserves every original structural value outside its four writes. -/
theorem nativeLattice_targetCentering_read_other (refs : Refs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (zeroFree : refs.isZero.key ∉ other.storageKeys)
    (scratchFree : refs.scratch.key ∉ other.storageKeys)
    (belowFree : refs.belowHalf.key ∉ other.storageKeys)
    (outputFree : refs.output.key ∉ other.storageKeys) (store : Store ctx) :
    (step refs store).1.read other = store.read other :=
  (nativeLattice_targetCentering_selection_read_other refs other outputFree
    (decisionStore refs store)).trans
    (nativeLattice_targetCentering_decision_read_other refs other
      zeroFree scratchFree belowFree store)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering
