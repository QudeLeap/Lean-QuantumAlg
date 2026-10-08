/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.CycleSchedule
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Requirement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Examples

/-!
# Native arbitrary-target XOR exponentiation with internal work preparation

The incoming exponent and target may be in any normalized joint state.
The actual program prepares the missing identity-power and zero auxiliary
words, executes the literal selected-power gate list, and retains every live system.
Its independent complete state target includes every external reference.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The built-in algorithm gate language with no quantum or classical oracle access. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- Independent XOR exponentiation with internally allocated work words.

**Input.**

- One caller-supplied interface containing an exponentWidth-qubit exponent and a width-qubit
arbitrary XOR target, in any normalized mixed state and with any external
reference. A positive fitted modulus N and a unit base in ZMod N are compilation
parameters. Even N, N=1, exponentWidth=0, and width=0 are included. The caller
supplies no initialized work word and no canonical-target premise.

**Output.**

- The complete output retains the exponent, transformed target, and both internally
prepared words. On a basis input (x,t), the target becomes t XOR (base^x mod N),
the exponent remains x, and the work words return to (0,0). The full
joint-state target tensors the incoming state with that declared work basis
and applies the independent exact finite exponentiation operator, preserving
all relative phases and external reference correlations.

**Resource budget.**

- Every fresh work qubit contributes its actual zero-preparation event. The
independent native budget covers identity loading and unloading, selected-power
compute and uncompute, and the literal CNOT copy. Each native gate coordinate
is bounded by `8*exponentWidth*M(width)+3*width`, where `M` is the registered
multiplier envelope. Resident space is exponentWidth+3*width qubits, and
auxiliary space is the two prepared width-qubit words. The unit-duration depth
bound includes the preparation layer and the complete arithmetic gate schedule.

**Success.**

- The unit result has probability one. The complete reference-aware state
promise holds for every admitted input. Empty work layouts retain their actual
preparation event while allocating zero work systems. Every live entry appears
in the output, and borrowed-restoration obligations follow from the execution.

**Source.**

- The modular-power target and reversible XOR form follow the selected-power
construction [VBE95, 9511018.tex:372-416]. The implementation composes the
registered arithmetic components with literal selected-power controls, copying,
and inverse computation; its budgets follow the actual elementary event trace.
-/
public def problem (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Problem model (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [preparedRequirement exponentWidth width modulus positive base]
  resources :=
    { events := arithmeticPreparedNativeBudget exponentWidth width
      resident := space (exponentWidth + 3 * width)
      auxiliary := space (2 * width) }
  depth :=
    { duration := fun _ => 1
      limit := arithmeticPreparedNativeDepth exponentWidth width
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := fun coordinate => nomatch coordinate }

/-- Prepare the two work words, execute the actual XOR oracle, and retain every live entry. -/
public def algorithm (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm model (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  run :=
    { code := arithmeticNativeCode exponentWidth width modulus positive base
      output := Output.all (preparedContext exponentWidth width) .unit }

/-- Independent scalar ceiling for each actual native gate coordinate,
including identity loading, copying and the complete uncomputation. -/
@[expose] public def gidneyExponentiationGateCountBound (exponentWidth width : Nat) : Nat :=
  let offset := fun n => n * (39 * Nat.clog 2 n + 1)
  let modularOffset := 6 * offset (width + 1) + 30 * offset width + 24 * width + 18
  let stage := if width ≤ 2 then 9 else 4 * modularOffset
  8 * exponentWidth * (2 * width * stage + 3 * width) + 3 * width

/-- Every native coordinate is counted on the same named public execution. -/
public theorem gidneyExponentiation_nativeGateCount_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (coordinate : AlgorithmGate.Coordinate)
    (path : (algorithm exponentWidth width modulus positive base).run.code.Path) :
    ResourcePool.count (model := model) (.gate coordinate)
      ((algorithm exponentWidth width modulus positive base).run.code.resourcePool path) ≤
        gidneyExponentiationGateCountBound exponentWidth width :=
  by
    have offset : Addition.Gidney.modularOffsetEventBound width =
        6 * ((width + 1) * (39 * Nat.clog 2 (width + 1) + 1)) +
          30 * (width * (39 * Nat.clog 2 width + 1)) + 24 * width + 18 := by
      simp only [Addition.Gidney.modularOffsetEventBound, Addition.Gidney.pivotEventBound,
        Addition.Gidney.biFlipEventBound, Addition.Gidney.comparisonEventBound,
        Addition.Gidney.constantOffsetEventBound, Nat.add_comm 1 width]
      ring
    simpa only [algorithm, gidneyExponentiationGateCountBound, Multiplication.Gidney.eventBound,
      Multiplication.Accumulate.Gidney.stageEventBound, offset, Nat.mul_assoc] using
      arithmeticNativeCode_gate_count_le exponentWidth width modulus positive base coordinate path

/-- Both input fields and both internally prepared work words remain in the complete output. -/
public theorem gidneyExponentiation_output_listing (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (algorithm exponentWidth width modulus positive base).run.output.listing =
      (preparedContext exponentWidth width).keys := (rfl)

/-- The public problem includes its complete joint-state requirement. -/
public theorem gidneyExponentiation_stateRequirement_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).states.length = 1 := (rfl)

/-- The resident budget counts the supplied exponent and target plus exactly two prepared words. -/
public theorem gidneyExponentiation_resident_budget (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).resources.resident =
      space (exponentWidth + 3 * width) := (rfl)

/-- The supplied exponent and target are excluded from auxiliary space; only
the two internally prepared words are charged. -/
public theorem gidneyExponentiation_auxiliary_budget (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).resources.auxiliary =
      space (2 * width) := (rfl)

private theorem actual_borrowed (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) {Reference : Register}
    {H : Type} [Fintype H]
    (state : Execution.State (context (exponentWidth + width)) Reference (model.HiddenState × H)) :
    (arithmeticNativeCode exponentWidth width modulus positive base).BorrowedRestored
      Reference state
      ((arithmeticNativeCode exponentWidth width modulus positive base).execute
        Reference state) := by
  let : Subsingleton (context (exponentWidth + width)).borrowedClassicalShape.Value := by
    change Subsingleton (CShape.Value .unit)
    exact ⟨fun left right => by cases left; cases right; rfl⟩
  let preparation : Circuit model (context (exponentWidth + width))
      (preparedContext exponentWidth width) :=
    Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty)
      (context (exponentWidth + width)) workKey (workLayout exponentWidth width)
      (gidneyExponentWork_fresh exponentWidth width)
      (gidneyExponentWork_disjoint exponentWidth width)
  exact Circuit.borrowedRestored_seq preparation
    (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
      (arithmeticNativeUnitary exponentWidth width modulus positive base)) state
    (Circuit.borrowedRestored_prepareZero_noBorrowedQuantum
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty) rfl state workKey
      (workLayout exponentWidth width) (gidneyExponentWork_fresh exponentWidth width)
      (gidneyExponentWork_disjoint exponentWidth width))
    (Circuit.borrowedRestored_unitary_noBorrowed
      (operations := .empty) (classicalOracles := .empty) rfl rfl
      (arithmeticNativeUnitary exponentWidth width modulus positive base)
      (preparation.execute Reference state))

set_option maxHeartbeats 800000 in
-- The endpoint proof expands both the native execution trace and the borrowed-register
-- observation; the larger budget is confined to this theorem.
/-- Actual preparation and XOR exponentiation satisfy the complete independent native problem. -/
public theorem gidneyExponentiation_solves
    (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm.Solves (algorithm exponentWidth width modulus positive base)
      (problem exponentWidth width modulus positive base) := by
  constructor
  · intro Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialization requirement present
    have same : requirement = preparedRequirement exponentWidth width modulus positive base :=
      List.mem_singleton.mp present
    subst requirement
    exact gidneyExponentPreparedRequirement_holds exponentWidth width modulus positive base
      (Output.all (preparedContext exponentWidth width) .unit) input
  · intro Reference input _valid _initialization
    change Execution.observeBorrowedAfter
      (arithmeticNativeCode exponentWidth width modulus positive base) Reference
        ((arithmeticNativeCode exponentWidth width modulus positive base).execute Reference
          (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (actual_borrowed exponentWidth width modulus positive base
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_native_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_resident_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_auxiliary_bound exponentWidth width modulus positive base path
  · intro _Reference _input _valid _initialization path _supported
    exact arithmeticNativeCode_depth_bound exponentWidth width modulus positive base path

/-- The caller requests one complete exponentiation, including work preparation. -/
public def cycleProblem (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    CycleProblem model (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  outcome := problem exponentWidth width modulus positive base
  plan := .cycle (problem exponentWidth width modulus positive base)

/-- Internal preparation and arithmetic form one complete cycle with an
explicit complete output and actual borrowed-reference restoration. -/
def arithmeticCycleSchedule (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    Circuit.CycleSchedule
      (.cycle (problem exponentWidth width modulus positive base))
      (arithmeticNativeCode exponentWidth width modulus positive base) :=
  .complete _ {
    output := Output.all (preparedContext exponentWidth width) .unit
    certified := gidneyExponentiation_solves exponentWidth width modulus positive base }

/-- The independently specified native envelope bounds the complete declared
cycle on every path of the same arithmetic execution. -/
theorem arithmeticCycleDepth_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    (arithmeticCycleSchedule exponentWidth width modulus positive base).maximumCycleDepth
        (fun _ => 1) path ≤ arithmeticPreparedNativeDepth exponentWidth width := by
  exact arithmeticNativeCode_depth_bound exponentWidth width modulus positive base path

/-- The exact exponentiation meets both its complete state problem and fixed caller cycle. -/
public def cycleCertificate (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm.CycleSolves (algorithm exponentWidth width modulus positive base)
      (cycleProblem exponentWidth width modulus positive base) where
  correctness := gidneyExponentiation_solves exponentWidth width modulus positive base
  schedule := arithmeticCycleSchedule exponentWidth width modulus positive base
  entry := fun _ _ admitted => admitted

/-- The actual native algorithm realizes the independently stated unit-base problem. -/
theorem mainOfUnit (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    ∃ candidate, Algorithm.Solves candidate
      (problem exponentWidth width modulus positive base) :=
  ⟨algorithm exponentWidth width modulus positive base,
    gidneyExponentiation_solves exponentWidth width modulus positive base⟩

/-- **Modular exponentiation.** A positive fitted modulus and a bounded
coprime natural base determine the complete reversible XOR implementation.
The finite base representation is converted to a unit only from the stated
coprimality witness. -/
public theorem main (exponentWidth width N a : Nat) (positive : 0 < N)
    (fitted : N ≤ 2 ^ width) (_baseBound : a < N) (coprime : Nat.Coprime a N) :
    ∃ candidate, Algorithm.Solves candidate
      (problem exponentWidth width
        (⟨N, Nat.lt_succ_of_le fitted⟩ : Fin (2 ^ width + 1)) positive
        (ZMod.unitOfCoprime a coprime)) :=
  mainOfUnit exponentWidth width
    (⟨N, Nat.lt_succ_of_le fitted⟩ : Fin (2 ^ width + 1)) positive
    (ZMod.unitOfCoprime a coprime)

end

end QuantumAlg.MAU.Exponentiation.Gidney
