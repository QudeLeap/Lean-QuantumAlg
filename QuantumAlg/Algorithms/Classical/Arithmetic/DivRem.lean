/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.RelationalLaws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Borrowed.Support
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
# Fixed-width quotient and remainder

The endpoint allocates a retained quotient-and-remainder cell and executes one
native division instruction. Its admissible inputs have nonzero divisors in
every positive-probability classical block. The complete output retains both
operands and results, including all borrowed correlations with a reference.
Euclidean division is proved from the existing pure fixed-width arithmetic;
no quantum divider or division-by-zero result is asserted by this endpoint.
-/

namespace QuantumAlg.ClassicalEndpoints.Arithmetic.DivRem

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The numerator and divisor have independently declared unsigned widths. -/
public abbrev inputShape (numeratorWidth divisorWidth : Nat) : CShape :=
  .product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)

/-- The quotient uses the numerator width and the remainder the divisor width. -/
public abbrev outputShape (numeratorWidth divisorWidth : Nat) : CShape :=
  .product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)

/-- The actual borrowed input is stored under key zero. -/
@[reducible] public def inputContext (numeratorWidth divisorWidth : Nat) : RuntimeCtx .classical :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ (inputShape numeratorWidth divisorWidth) (by decide)

private lemma resultFresh (numeratorWidth divisorWidth : Nat) :
    (⟨1⟩ : StorageKey) ∉ (inputContext numeratorWidth divisorWidth).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The complete final context retains the input and the allocated result. -/
@[reducible] public def outputContext (numeratorWidth divisorWidth : Nat) : RuntimeCtx .classical :=
  (inputContext numeratorWidth divisorWidth).addRetained ⟨1⟩ (outputShape numeratorWidth
    divisorWidth) (resultFresh numeratorWidth divisorWidth)

/-- Read both actual input words without materializing another cell. -/
public def inputRef (numeratorWidth divisorWidth : Nat) : CInputRef (inputContext numeratorWidth
  divisorWidth) (inputShape numeratorWidth divisorWidth) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩ (inputShape numeratorWidth
    divisorWidth) (by decide))

private def resultWrite (numeratorWidth divisorWidth : Nat) :
    CWriteRef (outputContext numeratorWidth divisorWidth) (outputShape numeratorWidth
      divisorWidth) :=
  CWriteRef.retainedHead (inputContext numeratorWidth divisorWidth) ⟨1⟩ (outputShape
    numeratorWidth divisorWidth) (resultFresh numeratorWidth divisorWidth)

private def resultRead (numeratorWidth divisorWidth : Nat) :
    CInputRef (outputContext numeratorWidth divisorWidth) (outputShape numeratorWidth
      divisorWidth) :=
  .storage (resultWrite numeratorWidth divisorWidth).toCStorageRef

private def divRemOp (numeratorWidth divisorWidth : Nat) :
    ClassicalOp (inputShape numeratorWidth divisorWidth) (outputShape numeratorWidth divisorWidth)
      (outputContext numeratorWidth divisorWidth) (outputContext numeratorWidth divisorWidth) :=
  .divRem numeratorWidth divisorWidth (outputContext numeratorWidth divisorWidth)
    ((inputRef numeratorWidth divisorWidth).underRetained ⟨1⟩ (outputShape numeratorWidth
      divisorWidth) (resultFresh numeratorWidth divisorWidth))
    (resultWrite numeratorWidth divisorWidth)

private def code (numeratorWidth divisorWidth : Nat) :
    Circuit (.classical BitWord.model .empty)
      (inputContext numeratorWidth divisorWidth) (outputContext numeratorWidth divisorWidth) :=
  .seq (.retain (model := .classical BitWord.model .empty)
    (inputContext numeratorWidth divisorWidth) ⟨1⟩ (outputShape numeratorWidth divisorWidth)
      (resultFresh numeratorWidth divisorWidth))
    (BitWord.instruction (execution := .classical BitWord.model .empty)
      (divRemOp numeratorWidth divisorWidth))

/-- The actual divisor is nonzero in every supported local input block. -/
@[expose] public def valid (numeratorWidth divisorWidth : Nat)
    (state : ExecutionState (Execution.Store (inputContext numeratorWidth divisorWidth))
      (inputContext numeratorWidth divisorWidth).register) : Prop :=
  ∀ store, 0 < (state.block store).mass →
    (store.read (inputRef numeratorWidth divisorWidth)).second.toNat ≠ 0

/-- Exact Euclidean division of the actual initial operands, including the valid divisor. -/
@[expose] public def accepts (numeratorWidth divisorWidth : Nat)
    (store : Execution.Store (inputContext numeratorWidth divisorWidth))
    (output : (outputShape numeratorWidth divisorWidth).Value) : Prop :=
  let input := store.read (inputRef numeratorWidth divisorWidth)
  input.second.toNat ≠ 0 ∧
    output.first.toNat * input.second.toNat + output.second.toNat = input.first.toNat ∧
    output.second.toNat < input.second.toNat

/-- Independent quotient-and-remainder specification.

**Input.** An unsigned `numeratorWidth`-bit numerator and an unsigned
`divisorWidth`-bit divisor. Every positive-probability input block must have a
nonzero divisor. This domain admits correlated inputs and every reference
extension of the same local state.
**Output.** Quotient in the numerator width and remainder in the divisor width,
with exact reconstruction and remainder below the divisor. The complete
manifest retains the input and both results.
**Resource budget.** One native classical `divRem numeratorWidth divisorWidth`
event; at most `2 * (numeratorWidth + divisorWidth)` resident and
`numeratorWidth + divisorWidth` auxiliary classical bits. No quantum systems
or depth are needed.
**Success.** The Euclidean relation holds with probability one, and every
borrowed input correlation with any external reference is restored.
**Source.** The pure fixed-width Euclidean division contract in
`QuantumAlg.Util.FixedWidth`; this supporting classical operation does not
claim a division circuit or gate count from the reversible-adder source VBE95.
-/
@[expose] public def problem (numeratorWidth divisorWidth : Nat) :
    Problem (.classical BitWord.model .empty) (inputContext numeratorWidth divisorWidth)
      (outputContext numeratorWidth
      divisorWidth) (outputShape numeratorWidth divisorWidth) where
  Witness := Unit
  valid := fun _ _ => valid numeratorWidth divisorWidth
  initialization := fun _ _ _ => True
  accepts := fun _ _ => accepts numeratorWidth divisorWidth
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources :=
    { events := ResourcePool.singleton (model := .classical BitWord.model .empty)
        (.classicalOperation (.divRem numeratorWidth divisorWidth))
      resident := fun .classicalBits => 2 * (numeratorWidth + divisorWidth)
      auxiliary := fun .classicalBits => numeratorWidth + divisorWidth }
  quantumTimeLimit := 0

/-- Allocate both results, divide the actual operands, and list every live key. -/
public def algorithm (numeratorWidth divisorWidth : Nat) :
    Algorithm (.classical BitWord.model .empty) (inputContext numeratorWidth divisorWidth)
      (outputContext numeratorWidth
      divisorWidth) (outputShape numeratorWidth divisorWidth) where
  run :=
    { code := code numeratorWidth divisorWidth
      output := Output.all (outputContext numeratorWidth divisorWidth) (.read (resultRead
        numeratorWidth divisorWidth)) }

private def finalStore (numeratorWidth divisorWidth : Nat) (store : Execution.Store (inputContext
  numeratorWidth divisorWidth)) :
    Execution.Store (outputContext numeratorWidth divisorWidth) :=
  (store.pushRetained ⟨1⟩ (outputShape numeratorWidth divisorWidth) (resultFresh numeratorWidth
    divisorWidth)).applyOp (divRemOp numeratorWidth divisorWidth)

private lemma finalStore_result (numeratorWidth divisorWidth : Nat) (store : Execution.Store
  (inputContext numeratorWidth divisorWidth)) :
    (finalStore numeratorWidth divisorWidth store).read (resultRead numeratorWidth divisorWidth) =
      CShape.divRem numeratorWidth divisorWidth (store.read (inputRef numeratorWidth
        divisorWidth)) := by
  change ((store.pushRetained ⟨1⟩ (outputShape numeratorWidth divisorWidth) (resultFresh
    numeratorWidth divisorWidth)).applyOp
    (divRemOp numeratorWidth divisorWidth)).read (.storage (divRemOp numeratorWidth
      divisorWidth).outputRef.toCStorageRef) = _
  rw [Execution.Store.read_applyOp_output]
  change CShape.divRem numeratorWidth divisorWidth
    ((store.pushRetained ⟨1⟩ (outputShape numeratorWidth divisorWidth) (resultFresh numeratorWidth
      divisorWidth)).read
      ((inputRef numeratorWidth divisorWidth).underRetained ⟨1⟩ (outputShape numeratorWidth
        divisorWidth) (resultFresh numeratorWidth divisorWidth))) = _
  rw [Execution.Store.read_pushRetained_underRetained]

private lemma divRem_arithmetic (numeratorWidth divisorWidth : Nat)
    (input : (inputShape numeratorWidth divisorWidth).Value)
    (inputValid : input.second.toNat ≠ 0) :
    let output := CShape.divRem numeratorWidth divisorWidth input
    input.second.toNat ≠ 0 ∧
      output.first.toNat * input.second.toNat + output.second.toNat = input.first.toNat ∧
      output.second.toNat < input.second.toNat := by
  cases input with
  | product numerator divisor =>
      cases numerator with
      | unsignedWord numerator =>
          cases divisor with
          | unsignedWord divisor =>
              exact ClassicalAlgorithms.DivRem.divRem_eval_accepts
                { numerator := numerator, divisor := divisor } inputValid

private lemma finalStore_accepts (numeratorWidth divisorWidth : Nat)
    (store : Execution.Store (inputContext numeratorWidth divisorWidth))
    (inputValid : (store.read (inputRef numeratorWidth divisorWidth)).second.toNat ≠ 0) :
    accepts numeratorWidth divisorWidth store
      ((finalStore numeratorWidth divisorWidth store).read
        (resultRead numeratorWidth divisorWidth)) := by
  unfold accepts
  rw [finalStore_result]
  exact divRem_arithmetic numeratorWidth divisorWidth
    (store.read (inputRef numeratorWidth divisorWidth)) inputValid

private lemma actual_events (numeratorWidth divisorWidth : Nat) (path : (code numeratorWidth
  divisorWidth).Path) :
    (code numeratorWidth divisorWidth).resourcePool path =
      ResourcePool.singleton (model := .classical BitWord.model .empty) (.classicalOperation
        (.divRem numeratorWidth divisorWidth)) := by
  change ResourcePool.ofList (model := .classical BitWord.model .empty) [.classicalOperation
    (.divRem numeratorWidth divisorWidth)] = _
  simp

private lemma actual_resident (numeratorWidth divisorWidth : Nat)
    (path : (code numeratorWidth divisorWidth).Path) :
    (code numeratorWidth divisorWidth).peakResidentSpace path ≤
      (fun .classicalBits => 2 * (numeratorWidth + divisorWidth) : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max (numeratorWidth + divisorWidth)
    (Nat.max (numeratorWidth + divisorWidth + (numeratorWidth + divisorWidth))
      (Nat.max (numeratorWidth + divisorWidth + (numeratorWidth + divisorWidth)) 0)) ≤
    2 * (numeratorWidth + divisorWidth)
  simp only [Nat.max_zero, Nat.max_self]
  exact max_le (by omega) (by omega)

private lemma actual_auxiliary (numeratorWidth divisorWidth : Nat)
    (path : (code numeratorWidth divisorWidth).Path) :
    (code numeratorWidth divisorWidth).peakAuxiliarySpace path ≤
      (fun .classicalBits => numeratorWidth + divisorWidth : SpacePool .classical) := by
  intro axis
  cases axis
  change Nat.max 0 (Nat.max (numeratorWidth + divisorWidth)
    (Nat.max (numeratorWidth + divisorWidth) 0)) ≤ numeratorWidth + divisorWidth
  simpa only [Nat.max_zero, Nat.max_self, Nat.zero_max] using
    Nat.le_refl (numeratorWidth + divisorWidth)

private def finalRecord (numeratorWidth divisorWidth : Nat)
    (entry : Execution.Store (inputContext numeratorWidth divisorWidth) ×
      ClassicalOracleModel.empty.HiddenState) :
    (algorithm numeratorWidth divisorWidth).run.Record :=
  let retained := entry.1.pushRetained ⟨1⟩ (outputShape numeratorWidth divisorWidth) (resultFresh
    numeratorWidth divisorWidth)
  let result := BitWord.instructionStep
    (execution := .classical BitWord.model .empty) (divRemOp numeratorWidth divisorWidth) retained
  (result.1, (entry.2, (entry.1, ((), result.2))))

private lemma execution_eq_map (numeratorWidth divisorWidth : Nat)
    (environment : (ExecutionModel.classical BitWord.model .empty).Environment)
    (Reference : Register)
    (state : ExecutionState
      (Execution.Store (inputContext numeratorWidth divisorWidth) ×
        ClassicalOracleModel.empty.HiddenState)
      (Register.prod (inputContext numeratorWidth divisorWidth).register Reference)) :
    (algorithm numeratorWidth divisorWidth).run.execute environment Reference state =
      state.mapClassical
      (finalRecord numeratorWidth divisorWidth) := by
  simp only [algorithm, AlgorithmRun.execute, code, Circuit.execute_seq,
    Circuit.execute_retain, BitWord.bitWord_instruction_execute,
    Execution.State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma relational_distribution (numeratorWidth divisorWidth : Nat)
    (environment : (ExecutionModel.classical BitWord.model .empty).Environment)
    {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext numeratorWidth divisorWidth) Reference) :
    (algorithm numeratorWidth divisorWidth).relationalDistribution environment input =
      (input.state.toPMF input.normalized).map
        (fun store => (store.1, (finalStore numeratorWidth divisorWidth store.1).read (resultRead
          numeratorWidth divisorWidth))) := by
  apply AlgorithmRun.relationalDistribution_eq_map_of_block_mass
    (algorithm numeratorWidth divisorWidth).run environment input
    (finalRecord numeratorWidth divisorWidth)
  intro record
  rw [execution_eq_map]

private lemma success_probability (numeratorWidth divisorWidth : Nat)
    (environment : (ExecutionModel.classical BitWord.model .empty).Environment)
    {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext numeratorWidth divisorWidth) Reference)
    (inputValid : valid numeratorWidth divisorWidth input.caller.localState) :
    (1 : ENNReal) ≤ ((algorithm numeratorWidth divisorWidth).relationalDistribution environment
      input).toOuterMeasure
      {pair | accepts numeratorWidth divisorWidth pair.1 pair.2} := by
  rw [relational_distribution]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨store, inputSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  apply finalStore_accepts numeratorWidth divisorWidth store.1
  apply inputValid store.1
  exact input.caller_local_mass_pos_of_joint store
    ((ExecutionState.mem_support_toPMF_iff input.state input.normalized store).mp inputSupported)

private lemma restores_borrowed (numeratorWidth divisorWidth : Nat)
    (environment : (ExecutionModel.classical BitWord.model .empty).Environment)
    {Reference : Register}
    (input : Execution.OracleInput .empty (inputContext numeratorWidth divisorWidth) Reference) :
    (algorithm numeratorWidth divisorWidth).run.RestoresBorrowed environment input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (code numeratorWidth divisorWidth) environment (by rfl) reference state

/-- Native division solves the independent nonzero-divisor arithmetic and storage contract. -/
public theorem main (numeratorWidth divisorWidth : Nat) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
  (problem numeratorWidth divisorWidth) := by
  refine ⟨algorithm numeratorWidth divisorWidth, ?_⟩
  constructor
  · intro environment _witness Reference input inputValid _initialization
    exact success_probability numeratorWidth divisorWidth environment input inputValid
  · intro _environment _witness _Reference _input _valid _initialization _requirement impossible
    cases impossible
  · intro environment _witness Reference input _valid _initialization
    exact restores_borrowed numeratorWidth divisorWidth environment input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events numeratorWidth divisorWidth path)
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_resident numeratorWidth divisorWidth path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_auxiliary numeratorWidth divisorWidth path
  · intro _environment _witness _Reference _input _valid _initialization _path _supported
    exact le_of_eq (Circuit.quantumTime_classicalModel _ _)

end

end QuantumAlg.ClassicalEndpoints.Arithmetic.DivRem
