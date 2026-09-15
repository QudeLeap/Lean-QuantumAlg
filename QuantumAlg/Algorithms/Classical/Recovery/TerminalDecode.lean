/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Classical.Endpoint
public import QuantumAlg.Util.Classical.TerminalDecode
public import Mathlib.Data.Multiset.Replicate
import all QuantumAlg.Algorithms.Classical.Endpoint
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.RelationalLaws
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics

/-!
# Fixed-order terminal decoding through actual classical storage

The decoder allocates its result, shifts the accumulator once for each source
bit, and selects an increment only when that stored bit is true. The complete
output retains the borrowed input and actual result, including at width zero.
The binary-value convention is [dW19, qcnotes.tex:8125]; the native instruction
schedule and storage allowances below are derived from this implementation.
-/

namespace QuantumAlg.ClassicalEndpoints.Recovery.TerminalDecode

open ClassicalAlgorithms.TerminalDecode
open ClassicalRoutines.TerminalDecode

/-- Read the borrowed bit string without computing or allocating another value. -/
public def inputRef (width : Nat) : CInputRef (Standard.pre (.bits width)) (.bits width) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩ (.bits width) (by decide))

/-- The output is the exact binary value in the declared source order. -/
@[expose] public def accepts (width : Nat) (order : BitOrder)
    (store : Execution.Store (Standard.pre (.bits width)))
    (output : CShape.Value (.unsignedWord width)) : Prop :=
  let bits := fun index => (store.read (.bitsGet (inputRef width) index)).toBool
  output.toNat = match order with
    | .bigEndian => Nat.ofBits (bits ∘ Fin.rev)
    | .littleEndian => Nat.ofBits bits

/-- Independent total terminal-decoding specification.

**Input.**
- A borrowed $w$-bit string and either declared bit order. All intrinsic inputs
  are admitted, including width zero and arbitrary external-reference correlations.
**Output.**
- The corresponding unsigned $w$-bit integer. The complete output retains the
  original borrowed bit string and the actual result word.
**Resource budget.**
- Exactly $w$ native shifts and at most $w$ selected increments, with both
  operation coordinates and their width retained.
- At most $2w$ resident and $w$ auxiliary classical bits; no quantum systems
  or quantum depth.
**Success.**
- The exact binary-value relation holds with probability one, while the borrowed
  input preserves its full joint state with every external reference.
**Source.**
- [dW19, qcnotes.tex:8125] fixes the integer/bitstring convention.
  The shift/increment execution and concrete memory allowances are project-derived.
-/
@[expose] public def problem (width : Nat) (order : BitOrder) :
    Problem .classical (Standard.pre (.bits width))
      (Standard.post (.bits width) (.unsignedWord width)) (.unsignedWord width) where
  valid := fun _ => True
  accepts := accepts width order
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := width •
        (Multiset.replicate 1 (.classicalOperation (.wordUnary .shiftLeft width)) +
          Multiset.replicate 1 (.classicalOperation (.wordUnary .increment width)))
      resident := fun .classicalBits => 2 * width
      auxiliary := fun .classicalBits => width }
  depth := .classical

/-- Allocate one real result word and execute the stored-bit shift/increment fold. -/
public def algorithm (width : Nat) (order : BitOrder) :
    Algorithm .classical (Standard.pre (.bits width))
      (Standard.post (.bits width) (.unsignedWord width)) (.unsignedWord width) where
  run := ClassicalRoutines.TerminalDecode.run (Standard.pre (.bits width)) width order
    (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width))

/-- The complete output includes every final live key, with its original storage role. -/
public theorem terminalDecodeEndpoint_output_listing (width : Nat) (order : BitOrder) :
    (algorithm width order).run.output.listing =
      (Standard.post (.bits width) (.unsignedWord width)).keys := by
  exact terminalDecode_run_output_listing (Standard.pre (.bits width)) width order
    (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width))

private def code (width : Nat) (order : BitOrder) := (algorithm width order).run.code

private noncomputable def finalStore (width : Nat) (order : BitOrder)
    (store : Execution.Store (Standard.pre (.bits width))) :
    Execution.Store (Standard.post (.bits width) (.unsignedWord width)) :=
  (retainedStep (Standard.pre (.bits width)) width order (inputRef width)
    Standard.resultKey (Standard.resultFresh (.bits width)) store).1

private theorem finalStore_accepts (width : Nat) (order : BitOrder)
    (store : Execution.Store (Standard.pre (.bits width))) :
    accepts width order store ((finalStore width order store).read
      (Standard.resultRef (.bits width) (.unsignedWord width))) := by
  have decoded := congrArg Fin.val (terminalDecode_retainedStep_read_output
    (Standard.pre (.bits width)) width order (inputRef width) Standard.resultKey
    (Standard.resultFresh (.bits width)) store)
  rw [terminalDecode_decodeOutput_val] at decoded
  unfold accepts
  refine decoded.trans ?_
  cases source : store.read (inputRef width) with
  | bits bits =>
      cases order <;> simp [decodeInput, eval, decodeNat_bigEndian,
        decodeNat_littleEndian, source, Execution.Store.read,
        CShape.Value.bitGet, CShape.Value.toBool]

private theorem actual_resident (width : Nat) (order : BitOrder)
    (path : (code width order).Path) :
    (code width order).peakResidentSpace path ≤
      (fun .classicalBits => 2 * width : SpacePool .classical) := by
  refine (terminalDecode_routine_resident_le (Standard.pre (.bits width)) width order
    (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width)) path).trans ?_
  intro axis
  cases axis
  change width + width ≤ 2 * width
  omega

private theorem actual_auxiliary (width : Nat) (order : BitOrder)
    (path : (code width order).Path) :
    (code width order).peakAuxiliarySpace path ≤
      (fun .classicalBits => width : SpacePool .classical) := by
  refine (terminalDecode_routine_auxiliary_le (Standard.pre (.bits width)) width order
    (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width)) path).trans ?_
  intro axis
  cases axis
  exact Nat.le_refl width

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def finalRecord (width : Nat) (order : BitOrder)
    (store : Execution.Store (Standard.pre (.bits width))) :
    (algorithm width order).run.Record :=
  (finalStore width order store, (store,
    (retainedStep (Standard.pre (.bits width)) width order (inputRef width)
      Standard.resultKey (Standard.resultFresh (.bits width)) store).2))

private theorem execution_eq_map (width : Nat) (order : BitOrder) (Reference : Register)
    (state : ExecutionState (Execution.Store (Standard.pre (.bits width)))
      (Register.prod (Standard.pre (.bits width)).register Reference)) :
    (algorithm width order).run.execute Reference state =
      state.mapClassical (finalRecord width order) := by
  change (routine (Standard.pre (.bits width)) width order (inputRef width)
    Standard.resultKey (Standard.resultFresh (.bits width))).execute Reference
      (state.mapClassical (fun store => (store, store))) = _
  rw [terminalDecode_routine_execute]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  rfl

private theorem relational_distribution (width : Nat) (order : BitOrder)
    {Reference : Register} (input : Execution.Input (Standard.pre (.bits width)) Reference) :
    (algorithm width order).relationalDistribution input =
      (input.state.toPMF input.normalized).map (fun store =>
        (store, (finalStore width order store).read
          (Standard.resultRef (.bits width) (.unsignedWord width)))) := by
  apply AlgorithmRun.relationalDistribution_eq_map_of_block_mass
    (algorithm width order).run input (finalRecord width order)
  intro record
  exact congrArg (fun state => (state.block record).mass)
    (execution_eq_map width order Reference input.state)

private theorem success_probability (width : Nat) (order : BitOrder)
    {Reference : Register} (input : Execution.Input (Standard.pre (.bits width)) Reference) :
    (1 : ENNReal) ≤ ((algorithm width order).relationalDistribution input).toOuterMeasure
      {pair | accepts width order pair.1 pair.2} := by
  rw [relational_distribution]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨store, _inputSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact finalStore_accepts width order store

/-- The named decoder meets the independent contract for both orders and every width. -/
public theorem main (width : Nat) (order : BitOrder) :
    (algorithm width order).Solves (problem width order) := by
  constructor
  · intro Reference input _valid
    exact success_probability width order input
  · intro _Reference _input _valid _requirement impossible
    cases impossible
  · intro Reference input _valid
    exact terminalDecode_routine_borrowedRestored (Standard.pre (.bits width)) width order
      (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width)) Reference
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact terminalDecode_routine_pool_le (Standard.pre (.bits width)) width order
      (inputRef width) Standard.resultKey (Standard.resultFresh (.bits width)) path
  · intro _Reference _input _valid path _supported
    exact actual_resident width order path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary width order path
  · intro _Reference _input _valid _path _supported
    trivial

end

end QuantumAlg.ClassicalEndpoints.Recovery.TerminalDecode
