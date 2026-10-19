/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Program

/-!
# Actual natural remainder, acceptance bit and unconditional caller frame

Exact natural arithmetic retains the nonzero-divisor and supplied-zero
assumptions. The structural frame holds independently of all numerical data.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {numeratorWidth divisorWidth : Nat}

/-- The actual native division stores the exact natural remainder for a nonzero divisor. -/
lemma divide_remainder (refs : Refs ctx numeratorWidth divisorWidth) (store : Store ctx)
    (nonzero : (store.read refs.divisor).toNat ≠ 0) :
    ((store.applyOp (divideOp refs)).read (remainderInput refs)).toNat =
      (store.read refs.numerator).toNat % (store.read refs.divisor).toNat := by
  change (((store.applyOp (divideOp refs)).read
    (.storage (divideOp refs).outputRef.toCStorageRef)).second).toNat = _
  rw [Store.read_applyOp_output]
  exact ClassicalOp.eval_divRem_remainder_exact numeratorWidth divisorWidth ctx
    (.product refs.numerator refs.divisor) refs.division
    (.product (store.read refs.numerator) (store.read refs.divisor)) nonzero

/-- Native equality writes the comparison of the real remainder and supplied zero reads. -/
lemma check_accepted (refs : Refs ctx numeratorWidth divisorWidth) (store : Store ctx) :
    ((store.applyOp (checkOp refs)).read (writeInput refs.accepted)).toBool =
      decide ((store.read (remainderInput refs)).toNat = (store.read refs.zero).toNat) := by
  change ((store.applyOp (checkOp refs)).read
    (.storage (checkOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Both actual writes preserve every caller read outside their keys, for all numerical inputs. -/
lemma into_callerFrame (refs : Refs ctx numeratorWidth divisorWidth) (store : Store ctx) :
    CallerFrame refs store (step (model := model) refs store).1 := by
  intro shape other avoidsDivision avoidsAccepted
  change (((store.applyOp (divideOp refs)).applyOp (checkOp refs)).read other) = _
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (checkOp refs) other avoidsAccepted).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (divideOp refs) other avoidsDivision)

/-- The original supplied zero input is preserved as a complete structural value. -/
lemma into_zero_preserved (refs : Refs ctx numeratorWidth divisorWidth)
    (separation : Separation refs) (store : Store ctx) :
    (step (model := model) refs store).1.read refs.zero = store.read refs.zero :=
  into_callerFrame refs store refs.zero separation.zeroAvoidsDivision separation.zeroAvoidsAccepted

/-- The actual comparison write preserves the exact natural remainder computed by division. -/
lemma into_remainder (refs : Refs ctx numeratorWidth divisorWidth)
    (separation : Separation refs) (store : Store ctx)
    (nonzero : (store.read refs.divisor).toNat ≠ 0) :
    ((step (model := model) refs store).1.read (remainderInput refs)).toNat =
      (store.read refs.numerator).toNat % (store.read refs.divisor).toNat := by
  change (((store.applyOp (divideOp refs)).applyOp (checkOp refs)).read
    (remainderInput refs)).toNat = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (checkOp refs) (remainderInput refs)
    separation.divisionAvoidsAccepted]
  exact divide_remainder refs store nonzero

/-- The actual acceptance bit is exactly the original natural divisibility predicate. -/
lemma into_accepted (refs : Refs ctx numeratorWidth divisorWidth)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions store refs) :
    ((step (model := model) refs store).1.read (writeInput refs.accepted)).toBool =
      decide ((store.read refs.numerator).toNat % (store.read refs.divisor).toNat = 0) := by
  change (((store.applyOp (divideOp refs)).applyOp (checkOp refs)).read
    (writeInput refs.accepted)).toBool = _
  rw [check_accepted, divide_remainder refs store (Nat.ne_of_gt initial.1),
    Store.read_applyOp_of_not_mem_storageKeys store (divideOp refs) refs.zero
      separation.zeroAvoidsDivision, initial.2]

/-- The actual record meets the complete contract on the unchanged original numerical domain. -/
lemma into_correct (refs : Refs ctx numeratorWidth divisorWidth)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions store refs) : Relation refs store (step (model := model) refs
      store).1 :=
  ⟨into_remainder refs separation store (Nat.ne_of_gt initial.1),
    into_accepted refs separation store initial, into_callerFrame refs store⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
