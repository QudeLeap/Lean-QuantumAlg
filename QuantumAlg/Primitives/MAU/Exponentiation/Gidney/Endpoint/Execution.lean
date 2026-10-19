/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Problem

import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Requirement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Examples
public import Mathlib.Analysis.SpecialFunctions.Log.Base

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

/-- Prepare the two work words, execute the actual XOR oracle, and retain every live entry. -/
public def algorithm (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm model (context (exponentWidth + width)) (preparedContext exponentWidth width)
      .unit where
  run :=
    { code := arithmeticNativeCode exponentWidth width modulus positive base
      output := Output.all (preparedContext exponentWidth width) .unit }

private lemma actual_borrowed (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    {environment : model.Environment} {Reference : Register}
    {H : Type} [Fintype H]
    (state : Execution.State (context (exponentWidth + width)) Reference (model.HiddenState × H)) :
    (arithmeticNativeCode exponentWidth width modulus positive base).BorrowedRestored
      Reference state
      ((arithmeticNativeCode exponentWidth width modulus positive base).execute
        environment Reference state) := by
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
  exact Circuit.borrowedRestored_seq environment preparation
    (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
      (arithmeticNativeUnitary exponentWidth width modulus positive base)) state
    (Circuit.borrowedRestored_prepareZero_noBorrowedQuantum
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty) rfl environment state workKey
      (workLayout exponentWidth width) (gidneyExponentWork_fresh exponentWidth width)
      (gidneyExponentWork_disjoint exponentWidth width))
    (Circuit.borrowedRestored_unitary_noBorrowed
      (operations := .empty) (classicalOracles := .empty) environment rfl rfl
      (arithmeticNativeUnitary exponentWidth width modulus positive base)
      (preparation.execute environment Reference state))

end

end QuantumAlg.MAU.Exponentiation.Gidney
