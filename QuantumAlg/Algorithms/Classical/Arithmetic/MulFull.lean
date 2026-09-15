/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.RelationalLaws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Util.Classical.Arithmetic

/-!
# Full-width classical multiplication

The endpoint allocates a result whose width is the sum of its operand widths
and executes one native multiplication instruction. Its complete output keeps
both the borrowed operands and the exact product. These classical arithmetic
semantics support the reversible-arithmetic setting of [VBE95,
9511018.tex:327-369]; its one native event is not a quantum gate count.
-/

namespace QuantumAlg.ClassicalEndpoints.Arithmetic.MulFull

/-- Two unsigned words with independently declared widths. -/
public abbrev inputShape (leftWidth rightWidth : Nat) : CShape :=
  .product (.unsignedWord leftWidth) (.unsignedWord rightWidth)

/-- The full product uses the sum of the operand widths. -/
public abbrev outputShape (leftWidth rightWidth : Nat) : CShape :=
  .unsignedWord (leftWidth + rightWidth)

/-- The actual borrowed input is stored under key zero. -/
@[reducible] public def inputContext (leftWidth rightWidth : Nat) : RuntimeCtx .classical :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ (inputShape leftWidth rightWidth) (by decide)

private theorem resultFresh (leftWidth rightWidth : Nat) :
    (⟨1⟩ : StorageKey) ∉ (inputContext leftWidth rightWidth).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The complete final context retains the input and the allocated result. -/
@[reducible] public def outputContext (leftWidth rightWidth : Nat) : RuntimeCtx .classical :=
  (inputContext leftWidth rightWidth).addRetained ⟨1⟩ (outputShape leftWidth rightWidth)
    (resultFresh leftWidth rightWidth)

/-- Read both actual input words without materializing another cell. -/
public def inputRef (leftWidth rightWidth : Nat) : CInputRef (inputContext leftWidth rightWidth)
  (inputShape leftWidth rightWidth) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩ (inputShape leftWidth rightWidth)
    (by decide))

private def resultWrite (leftWidth rightWidth : Nat) :
    CWriteRef (outputContext leftWidth rightWidth) (outputShape leftWidth rightWidth) :=
  CWriteRef.retainedHead (inputContext leftWidth rightWidth) ⟨1⟩ (outputShape leftWidth
    rightWidth) (resultFresh leftWidth rightWidth)

private def resultRead (leftWidth rightWidth : Nat) :
    CInputRef (outputContext leftWidth rightWidth) (outputShape leftWidth rightWidth) :=
  .storage (resultWrite leftWidth rightWidth).toCStorageRef

private def mulFullOp (leftWidth rightWidth : Nat) :
    ClassicalOp (inputShape leftWidth rightWidth) (outputShape leftWidth rightWidth)
      (outputContext leftWidth rightWidth) (outputContext leftWidth rightWidth) :=
  .mulFull leftWidth rightWidth (outputContext leftWidth rightWidth)
    ((inputRef leftWidth rightWidth).underRetained ⟨1⟩ (outputShape leftWidth rightWidth)
      (resultFresh leftWidth rightWidth))
    (resultWrite leftWidth rightWidth)

private def code (leftWidth rightWidth : Nat) : Circuit (inputContext leftWidth rightWidth)
  (outputContext leftWidth rightWidth) :=
  .seq (.retain (inputContext leftWidth rightWidth) ⟨1⟩ (outputShape leftWidth rightWidth)
    (resultFresh leftWidth rightWidth))
    (.classical (mulFullOp leftWidth rightWidth))

/-- The full result equals the product of the actual initial operands. -/
@[expose] public def accepts (leftWidth rightWidth : Nat)
    (store : Execution.Store (inputContext leftWidth rightWidth))
    (output : (outputShape leftWidth rightWidth).Value) : Prop :=
  let input := store.read (inputRef leftWidth rightWidth)
  output.toNat = input.first.toNat * input.second.toNat

/-- Independent full-width multiplication specification.

**Input.** An unsigned `leftWidth`-bit factor and an unsigned `rightWidth`-bit
factor. Every intrinsic pair is valid, including zero widths and correlated inputs.
**Output.** The exact product in `leftWidth + rightWidth` bits. The complete
manifest retains the borrowed input and the result.
**Resource budget.** One native classical `mulFull leftWidth rightWidth` event;
at most `2 * (leftWidth + rightWidth)` resident and `leftWidth + rightWidth`
auxiliary classical bits. No quantum systems or depth are needed.
**Success.** Exact multiplication holds with probability one, and the borrowed
input retains all joint correlations with any external reference.
**Source.** Classical arithmetic supporting the reversible multiplication in
[VBE95, 9511018.tex:327-369]; the native budget is independent of its gate costs.
-/
public def problem (leftWidth rightWidth : Nat) :
    Problem .classical (inputContext leftWidth rightWidth) (outputContext leftWidth rightWidth)
      (outputShape leftWidth rightWidth) where
  valid := fun _ => True
  accepts := accepts leftWidth rightWidth
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := ResourcePool.singleton (.classicalOperation (.mulFull leftWidth rightWidth))
      resident := fun .classicalBits => 2 * (leftWidth + rightWidth)
      auxiliary := fun .classicalBits => leftWidth + rightWidth }
  depth := .classical

/-- Allocate the full product, multiply the actual factors, and list every live key. -/
public def algorithm (leftWidth rightWidth : Nat) :
    Algorithm .classical (inputContext leftWidth rightWidth) (outputContext leftWidth rightWidth)
      (outputShape leftWidth rightWidth) where
  run :=
    { code := code leftWidth rightWidth
      output := Output.all (outputContext leftWidth rightWidth) (.read (resultRead leftWidth
        rightWidth)) }

private def finalStore (leftWidth rightWidth : Nat) (store : Execution.Store (inputContext
  leftWidth rightWidth)) :
    Execution.Store (outputContext leftWidth rightWidth) :=
  (store.pushRetained ⟨1⟩ (outputShape leftWidth rightWidth) (resultFresh leftWidth
    rightWidth)).applyOp (mulFullOp leftWidth rightWidth)

private theorem finalStore_result (leftWidth rightWidth : Nat) (store : Execution.Store
  (inputContext leftWidth rightWidth)) :
    (finalStore leftWidth rightWidth store).read (resultRead leftWidth rightWidth) =
      CShape.mulFull leftWidth rightWidth (store.read (inputRef leftWidth rightWidth)) := by
  change ((store.pushRetained ⟨1⟩ (outputShape leftWidth rightWidth) (resultFresh leftWidth
    rightWidth)).applyOp
    (mulFullOp leftWidth rightWidth)).read (.storage (mulFullOp leftWidth
      rightWidth).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.mulFull leftWidth rightWidth
    ((store.pushRetained ⟨1⟩ (outputShape leftWidth rightWidth) (resultFresh leftWidth
      rightWidth)).read
      ((inputRef leftWidth rightWidth).underRetained ⟨1⟩ (outputShape leftWidth rightWidth)
        (resultFresh leftWidth rightWidth))) = _
  rw [Execution.Store.read_pushRetained_underRetained]

private theorem mulFull_arithmetic (leftWidth rightWidth : Nat)
    (input : (inputShape leftWidth rightWidth).Value) :
    (CShape.mulFull leftWidth rightWidth input).toNat =
      input.first.toNat * input.second.toNat := by
  cases input with
  | product left right =>
      cases left with
      | unsignedWord left =>
          cases right with
          | unsignedWord right =>
              exact ClassicalAlgorithms.MulFull.mulFull_eval_accepts
                { left := left, right := right }

private theorem finalStore_accepts (leftWidth rightWidth : Nat) (store : Execution.Store
  (inputContext leftWidth rightWidth)) :
    accepts leftWidth rightWidth store ((finalStore leftWidth rightWidth store).read (resultRead
      leftWidth rightWidth)) := by
  unfold accepts
  rw [finalStore_result]
  exact mulFull_arithmetic leftWidth rightWidth (store.read (inputRef leftWidth rightWidth))

private theorem actual_events (leftWidth rightWidth : Nat) (path : (code leftWidth
  rightWidth).Path) :
    (code leftWidth rightWidth).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.mulFull leftWidth rightWidth)) := by
  change ResourcePool.ofList [.classicalOperation (.mulFull leftWidth rightWidth)] = _
  simp

private theorem actual_resident (leftWidth rightWidth : Nat)
    (path : (code leftWidth rightWidth).Path) :
    (code leftWidth rightWidth).peakResidentSpace path ≤
      (fun .classicalBits => 2 * (leftWidth + rightWidth) : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max (leftWidth + rightWidth)
    (Nat.max (leftWidth + rightWidth + (leftWidth + rightWidth))
      (Nat.max (leftWidth + rightWidth + (leftWidth + rightWidth)) 0)) ≤
    2 * (leftWidth + rightWidth)
  simp only [Nat.max_zero, Nat.max_self]
  exact max_le (by omega) (by omega)

private theorem actual_auxiliary (leftWidth rightWidth : Nat)
    (path : (code leftWidth rightWidth).Path) :
    (code leftWidth rightWidth).peakAuxiliarySpace path ≤
      (fun .classicalBits => leftWidth + rightWidth : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max 0 (Nat.max (leftWidth + rightWidth)
    (Nat.max (leftWidth + rightWidth) 0)) ≤ leftWidth + rightWidth
  simpa only [Nat.max_zero, Nat.max_self, Nat.zero_max] using
    Nat.le_refl (leftWidth + rightWidth)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def finalRecord (leftWidth rightWidth : Nat) (store : Execution.Store (inputContext
  leftWidth rightWidth)) :
    (algorithm leftWidth rightWidth).run.Record :=
  (finalStore leftWidth rightWidth store, (store, ((), ())))

private theorem execution_eq_map (leftWidth rightWidth : Nat) (Reference : Register)
    (state : ExecutionState (Execution.Store (inputContext leftWidth rightWidth))
      (Register.prod (inputContext leftWidth rightWidth).register Reference)) :
    (algorithm leftWidth rightWidth).run.execute Reference state = state.mapClassical (finalRecord
      leftWidth rightWidth) := by
  simp only [algorithm, AlgorithmRun.execute, code, Circuit.execute_seq,
    Circuit.execute_retain, Circuit.execute_classical, Execution.State.classicalStep,
    Execution.State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem relational_distribution (leftWidth rightWidth : Nat) {Reference : Register}
    (input : Execution.Input (inputContext leftWidth rightWidth) Reference) :
    (algorithm leftWidth rightWidth).relationalDistribution input =
      (input.state.toPMF input.normalized).map
        (fun store => (store, (finalStore leftWidth rightWidth store).read (resultRead leftWidth
          rightWidth))) := by
  apply AlgorithmRun.relationalDistribution_eq_map_of_block_mass
    (algorithm leftWidth rightWidth).run input (finalRecord leftWidth rightWidth)
  intro record
  rw [execution_eq_map]

private theorem success_probability (leftWidth rightWidth : Nat) {Reference : Register}
    (input : Execution.Input (inputContext leftWidth rightWidth) Reference) :
    (1 : ENNReal) ≤ ((algorithm leftWidth rightWidth).relationalDistribution input).toOuterMeasure
      {pair | accepts leftWidth rightWidth pair.1 pair.2} := by
  rw [relational_distribution]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨store, _inputSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact finalStore_accepts leftWidth rightWidth store

private theorem restores_borrowed (leftWidth rightWidth : Nat) {Reference : Register}
    (input : Execution.Input (inputContext leftWidth rightWidth) Reference) :
    (algorithm leftWidth rightWidth).run.RestoresBorrowed input := by
  change (code leftWidth rightWidth).BorrowedRestored Reference
    (input.state.mapClassical fun store => (store, store))
    ((code leftWidth rightWidth).execute Reference (input.state.mapClassical fun store => (store,
      store)))
  unfold code
  refine Circuit.borrowedRestored_seq _ _ _ ?_ ?_
  · exact Circuit.borrowedRestored_retain ⟨1⟩ (outputShape leftWidth rightWidth) (resultFresh
    leftWidth rightWidth) _
  · exact Circuit.borrowedRestored_classical (mulFullOp leftWidth rightWidth) _

/-- The native multiplication run solves the independent arithmetic and storage contract. -/
public theorem main (leftWidth rightWidth : Nat) : ∃ candidate, Algorithm.Solves candidate
  (problem leftWidth rightWidth) := by
  refine ⟨algorithm leftWidth rightWidth, ?_⟩
  constructor
  · intro Reference input _valid
    exact success_probability leftWidth rightWidth input
  · intro _Reference _input _valid _requirement impossible
    cases impossible
  · intro Reference input _valid
    exact restores_borrowed leftWidth rightWidth input
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events leftWidth rightWidth path)
  · intro _Reference _input _valid path _supported
    exact actual_resident leftWidth rightWidth path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary leftWidth rightWidth path
  · intro _Reference _input _valid _path _supported
    trivial

end

end QuantumAlg.ClassicalEndpoints.Arithmetic.MulFull
