/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
import all QuantumAlg.Core.Algorithm.RelationalLaws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Preservation
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Space

/-!
# Total native fixed-width GCD endpoint

The actual circuit allocates its result, executes the expanded Euclidean
schedule, releases each lexical cell and retains a complete output manifest.
The classical GCD used in factoring is described in [Sho95, source.tex:1132-1140].
The concrete native event and storage allowances below are proved from this
expanded implementation, rather than attributed to the paper.
-/

namespace QuantumAlg.ClassicalEndpoints.NumberTheory.GCD

open ClassicalRoutines.NumberTheory.GCD

/-- Two intrinsically bounded unsigned words, including the unique zero-width pair. -/
public abbrev inputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- One intrinsically bounded unsigned greatest-common-divisor result. -/
public abbrev outputShape (width : Nat) : CShape := .unsignedWord width

/-- The actual input pair is borrowed classical storage under key zero. -/
@[reducible] public def inputContext (width : Nat) : RuntimeCtx .classical :=
  RuntimeCtx.empty.addBorrowedInput ⟨0⟩ (inputShape width) (by decide)

private theorem resultFresh (width : Nat) :
    (⟨1⟩ : StorageKey) ∉ (inputContext width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- The final context keeps the complete borrowed pair and the actual retained result. -/
@[reducible] public def outputContext (width : Nat) : RuntimeCtx .classical :=
  (inputContext width).addRetained ⟨1⟩ (outputShape width) (resultFresh width)

/-- Read the existing input pair structurally. -/
public def inputRef (width : Nat) : CInputRef (inputContext width) (inputShape width) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩ (inputShape width) (by decide))

private def resultRead (width : Nat) : CInputRef (outputContext width) (outputShape width) :=
  retainedRead (inputContext width) width ⟨1⟩ (resultFresh width)

private def code (width : Nat) : Circuit (inputContext width) (outputContext width) :=
  retainedCircuit (inputRef width) ⟨1⟩ (resultFresh width)

/-- The actual unsigned output contains the greatest common divisor of the original operands. -/
@[expose] public def accepts (width : Nat) (store : Execution.Store (inputContext width))
    (output : (outputShape width).Value) : Prop :=
  output.toNat = Nat.gcd (store.read (inputRef width)).first.toNat
    (store.read (inputRef width)).second.toNat

/-- Independent total fixed-width GCD specification.

**Input.**
- Two unsigned `width`-bit integers; all intrinsic values, zero operands and
  width zero are admitted, with arbitrary classical-reference correlations.
**Output.**
- Their exact greatest common divisor as a `width`-bit word. The complete
  manifest retains both the borrowed input pair and the actual result.
**Resource budget.**
- Four initialization events, at most `2 * width + 1` five-event Euclidean
  iterations, and one final copy, with every native operation coordinate kept.
- At most `7 * width + 1` resident and `5 * width + 1` auxiliary classical
  bits, including the retained result and the temporary division pair.
- No quantum systems or quantum depth are required.
**Success.**
- The exact relation holds with probability one. The borrowed pair retains
  its complete joint correlations with every external reference.
**Source.**
- [Sho95, source.tex:1132-1140] uses classical Euclidean GCD in factoring.
  The concrete native allowances are derived from this expanded circuit.
-/
public def problem (width : Nat) :
    Problem .classical (inputContext width) (outputContext width) (outputShape width) where
  valid := fun _ => True
  accepts := accepts width
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := nativeEnvelope .classical width
      resident := fun .classicalBits => 7 * width + 1
      auxiliary := fun .classicalBits => 5 * width + 1 }
  depth := .classical

/-- Execute the expanded circuit and explicitly list every final live key. -/
public def algorithm (width : Nat) :
    Algorithm .classical (inputContext width) (outputContext width) (outputShape width) where
  run :=
    { code := code width
      output := Output.all (outputContext width) (.read (resultRead width)) }

/-- Both actual final live keys appear in the complete output manifest. -/
public theorem gcdNative_output_listing (width : Nat) :
    (algorithm width).run.output.listing = (outputContext width).keys := (rfl)

private noncomputable def finalStore (width : Nat) (store : Execution.Store (inputContext width)) :
    Execution.Store (outputContext width) :=
  (retainedStep (inputRef width) ⟨1⟩ (resultFresh width) store).1

private theorem finalStore_accepts (width : Nat) (store : Execution.Store (inputContext width)) :
    accepts width store ((finalStore width store).read (resultRead width)) := by
  unfold accepts
  have actual := congrArg CShape.Value.toNat
    (gcdRetained_read_result (inputRef width) ⟨1⟩ (resultFresh width) store)
  refine actual.trans ?_
  cases value : store.read (inputRef width) with
  | product left right =>
      cases left
      cases right
      rfl

private theorem actual_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤
      (fun .classicalBits => 7 * width + 1 : SpacePool .classical) := by
  refine (gcdRetained_resident_le (inputRef width) ⟨1⟩ (resultFresh width) path).trans ?_
  intro axis
  cases axis
  change (width + width) + (5 * width + 1) ≤ 7 * width + 1
  omega

private theorem actual_auxiliary (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤
      (fun .classicalBits => 5 * width + 1 : SpacePool .classical) := by
  refine (gcdRetained_auxiliary_le (inputRef width) ⟨1⟩ (resultFresh width) path).trans ?_
  intro axis
  cases axis
  change 0 + (5 * width + 1) ≤ 5 * width + 1
  omega

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def finalRecord (width : Nat) (store : Execution.Store (inputContext width)) :
    (algorithm width).run.Record :=
  (finalStore width store, (store, (retainedStep (inputRef width) ⟨1⟩ (resultFresh width) store).2))

private theorem execution_eq_map (width : Nat) (Reference : Register)
    (state : ExecutionState (Execution.Store (inputContext width))
      (Register.prod (inputContext width).register Reference)) :
    (algorithm width).run.execute Reference state = state.mapClassical (finalRecord width) := by
  let initial : Execution.State (inputContext width) Reference
      (Execution.Store (inputContext width)) :=
    state.mapClassical (fun store => (store, store))
  have executed : (algorithm width).run.execute Reference state =
      (retainedCircuit (inputRef width) ⟨1⟩ (resultFresh width)).execute Reference initial := by
    unfold AlgorithmRun.execute
    apply congrArg (fun entered : Execution.State (inputContext width) Reference
      (Execution.Store (inputContext width)) =>
        (retainedCircuit (inputRef width) ⟨1⟩ (resultFresh width)).execute Reference entered)
    congr 1
  refine executed.trans ((gcdRetained_execute (inputRef width) ⟨1⟩
    (resultFresh width) Reference initial).trans ?_)
  simp only [initial, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1

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

/-- The complete expanded native GCD algorithm meets its independent total contract. -/
public theorem main (width : Nat) : ∃ candidate, Algorithm.Solves candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro Reference input _valid
    exact success_probability width input
  · intro _Reference _input _valid _requirement impossible
    cases impossible
  · intro Reference input _valid
    exact gcdRetained_borrowedRestored (inputRef width) ⟨1⟩ (resultFresh width) Reference
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact gcdRetained_pool_le (inputRef width) ⟨1⟩ (resultFresh width) path
  · intro _Reference _input _valid path _supported
    exact actual_resident width path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width path
  · intro _Reference _input _valid _path _supported
    trivial

end

end QuantumAlg.ClassicalEndpoints.NumberTheory.GCD
