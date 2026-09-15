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
# Fixed-width subtraction with borrow

The endpoint allocates its retained result and executes one native subtraction
instruction on its two actual operands. Its complete output retains both the
borrowed input and the result. Subtraction is the reverse arithmetic relation
of the reversible addition discussed in [VBE95, 9511018.tex:267-282]. The native
classical event budget is independent of that paper's quantum gate costs.
-/

namespace QuantumAlg.ClassicalEndpoints.Arithmetic.SubBorrow

/-- Two unsigned words of the same declared width. -/
public abbrev inputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- The wrapped low word and the borrow out; there is no input borrow. -/
public abbrev outputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) .bit

/-- The actual borrowed input is stored under key zero. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .classical :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ (inputShape width) (by decide)

private theorem resultFresh (width : Nat) :
    (⟨1⟩ : StorageKey) ∉ (inputContext width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The complete final context retains the input and the allocated result. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .classical :=
  (inputContext width).addRetained ⟨1⟩ (outputShape width) (resultFresh width)

/-- Read both actual input words without materializing another cell. -/
public def inputRef (width : Nat) : CInputRef (inputContext width) (inputShape width) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩ (inputShape width) (by decide))

private def resultWrite (width : Nat) :
    CWriteRef (outputContext width) (outputShape width) :=
  CWriteRef.retainedHead (inputContext width) ⟨1⟩ (outputShape width) (resultFresh width)

private def resultRead (width : Nat) :
    CInputRef (outputContext width) (outputShape width) :=
  .storage (resultWrite width).toCStorageRef

private def subBorrowOp (width : Nat) :
    ClassicalOp (inputShape width) (outputShape width)
      (outputContext width) (outputContext width) :=
  .subBorrow width (outputContext width)
    ((inputRef width).underRetained ⟨1⟩ (outputShape width) (resultFresh width))
    (resultWrite width)

private def code (width : Nat) : Circuit (inputContext width) (outputContext width) :=
  .seq (.retain (inputContext width) ⟨1⟩ (outputShape width) (resultFresh width))
    (.classical (subBorrowOp width))

/-- Exact wrapped-difference reconstruction and borrow-out for the initial operands. -/
@[expose] public def accepts (width : Nat) (store : Execution.Store (inputContext width))
    (output : (outputShape width).Value) : Prop :=
  let input := store.read (inputRef width)
  input.first.toNat + output.second.toBool.toNat * 2 ^ width =
      input.second.toNat + output.first.toNat ∧
    output.second.toBool = decide (input.first.toNat < input.second.toNat)

/-- Independent subtraction-with-borrow specification.

**Input.** Two unsigned `width`-bit words, with no input borrow. All intrinsic
word values are allowed, including width zero and correlated classical inputs.
**Output.** The wrapped difference and outgoing borrow. The complete manifest
retains the borrowed input and the result.
**Resource budget.** One native classical `subBorrow width` event, at most
`3 * width + 1` resident and `width + 1` auxiliary classical bits. The retained
result contributes to auxiliary space. No quantum systems or depth are needed.
**Success.** Exact arithmetic holds with probability one; all borrowed input
correlations with any external reference are restored.
**Source.** Reverse arithmetic in [VBE95, 9511018.tex:267-282]. The native
classical instruction bound does not describe the paper's quantum gate count.
-/
public def problem (width : Nat) :
    Problem .classical (inputContext width) (outputContext width) (outputShape width) where
  valid := fun _ => True
  accepts := accepts width
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := ResourcePool.singleton (.classicalOperation (.subBorrow width))
      resident := fun .classicalBits => 3 * width + 1
      auxiliary := fun .classicalBits => width + 1 }
  depth := .classical

/-- Allocate the result, subtract the actual operands, and list every live key. -/
public def algorithm (width : Nat) :
    Algorithm .classical (inputContext width) (outputContext width) (outputShape width) where
  run :=
    { code := code width
      output := Output.all (outputContext width) (.read (resultRead width)) }

private def finalStore (width : Nat) (store : Execution.Store (inputContext width)) :
    Execution.Store (outputContext width) :=
  (store.pushRetained ⟨1⟩ (outputShape width) (resultFresh width)).applyOp (subBorrowOp width)

private theorem finalStore_result (width : Nat) (store : Execution.Store (inputContext width)) :
    (finalStore width store).read (resultRead width) =
      CShape.subBorrow width (store.read (inputRef width)) := by
  change ((store.pushRetained ⟨1⟩ (outputShape width) (resultFresh width)).applyOp
    (subBorrowOp width)).read (.storage (subBorrowOp width).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.subBorrow width
    ((store.pushRetained ⟨1⟩ (outputShape width) (resultFresh width)).read
      ((inputRef width).underRetained ⟨1⟩ (outputShape width) (resultFresh width))) = _
  rw [Execution.Store.read_pushRetained_underRetained]

private theorem subBorrow_arithmetic (width : Nat) (input : (inputShape width).Value) :
    let output := CShape.subBorrow width input
    input.first.toNat + output.second.toBool.toNat * 2 ^ width =
        input.second.toNat + output.first.toNat ∧
      output.second.toBool = decide (input.first.toNat < input.second.toNat) := by
  cases input with
  | product left right =>
      cases left with
      | unsignedWord left =>
          cases right with
          | unsignedWord right =>
              constructor
              · have reconstruct :=
                  ClassicalAlgorithms.SubBorrow.subBorrow_eval_reconstruct
                    { left := left, right := right }
                rw [ClassicalAlgorithms.SubBorrow.subBorrow_eval_borrow,
                  ClassicalAlgorithms.SubBorrow.subBorrow_eval_low_eq_wrapping]
                  at reconstruct
                exact reconstruct
              · rfl

private theorem finalStore_accepts (width : Nat) (store : Execution.Store (inputContext width)) :
    accepts width store ((finalStore width store).read (resultRead width)) := by
  unfold accepts
  rw [finalStore_result]
  exact subBorrow_arithmetic width (store.read (inputRef width))

private theorem actual_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path =
      ResourcePool.singleton (.classicalOperation (.subBorrow width)) := by
  change ResourcePool.ofList [.classicalOperation (.subBorrow width)] = _
  simp

private theorem actual_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤
      (fun .classicalBits => 3 * width + 1 : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max (width + width)
    (Nat.max (width + 1 + (width + width))
      (Nat.max (width + 1 + (width + width)) 0)) ≤ 3 * width + 1
  simp only [Nat.max_zero, Nat.max_self]
  exact max_le (by omega) (by omega)

private theorem actual_auxiliary (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤
      (fun .classicalBits => width + 1 : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max 0 (Nat.max (width + 1) (Nat.max (width + 1) 0)) ≤ width + 1
  simpa only [Nat.max_zero, Nat.max_self, Nat.zero_max] using Nat.le_refl (width + 1)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def finalRecord (width : Nat) (store : Execution.Store (inputContext width)) :
    (algorithm width).run.Record :=
  (finalStore width store, (store, ((), ())))

private theorem execution_eq_map (width : Nat) (Reference : Register)
    (state : ExecutionState (Execution.Store (inputContext width))
      (Register.prod (inputContext width).register Reference)) :
    (algorithm width).run.execute Reference state = state.mapClassical (finalRecord width) := by
  simp only [algorithm, AlgorithmRun.execute, code, Circuit.execute_seq,
    Circuit.execute_retain, Circuit.execute_classical, Execution.State.classicalStep,
    Execution.State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem relational_distribution (width : Nat) {Reference : Register}
    (input : Execution.Input (inputContext width) Reference) :
    (algorithm width).relationalDistribution input =
      (input.state.toPMF input.normalized).map
        (fun store => (store, (finalStore width store).read (resultRead width))) := by
  apply AlgorithmRun.relationalDistribution_eq_map_of_block_mass
    (algorithm width).run input (finalRecord width)
  intro record
  rw [execution_eq_map]

private theorem success_probability (width : Nat) {Reference : Register}
    (input : Execution.Input (inputContext width) Reference) :
    (1 : ENNReal) ≤ ((algorithm width).relationalDistribution input).toOuterMeasure
      {pair | accepts width pair.1 pair.2} := by
  rw [relational_distribution]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨store, _inputSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact finalStore_accepts width store

private theorem restores_borrowed (width : Nat) {Reference : Register}
    (input : Execution.Input (inputContext width) Reference) :
    (algorithm width).run.RestoresBorrowed input := by
  change (code width).BorrowedRestored Reference
    (input.state.mapClassical fun store => (store, store))
    ((code width).execute Reference (input.state.mapClassical fun store => (store, store)))
  unfold code
  refine Circuit.borrowedRestored_seq _ _ _ ?_ ?_
  · exact Circuit.borrowedRestored_retain ⟨1⟩ (outputShape width) (resultFresh width) _
  · exact Circuit.borrowedRestored_classical (subBorrowOp width) _

/-- The native subtraction run solves the independent arithmetic and storage contract. -/
public theorem main (width : Nat) : ∃ candidate, Algorithm.Solves candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro Reference input _valid
    exact success_probability width input
  · intro _Reference _input _valid _requirement impossible
    cases impossible
  · intro Reference input _valid
    exact restores_borrowed width input
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events width path)
  · intro _Reference _input _valid path _supported
    exact actual_resident width path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width path
  · intro _Reference _input _valid _path _supported
    trivial

end

end QuantumAlg.ClassicalEndpoints.Arithmetic.SubBorrow
