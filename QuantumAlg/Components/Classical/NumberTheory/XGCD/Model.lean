/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.NumberTheory.Extended

/-!
# Existing pure extended-Euclidean model names

This owner exposes the original pure input, result, recurrence, path, and
coefficient-width names used by the fixed-width XGCD component. It imports
only the pure mathematical model, with no machine or circuit implementation.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open ClassicalAlgorithms
open ClassicalAlgorithms.NumberTheory

/- A local namespace of transparent aliases keeps the pure executable model
visibly distinct from this component namespace. -/
namespace PureXGCD

/-- Pure extended-GCD input. -/
abbrev Input :=
  ClassicalAlgorithms.NumberTheory.XGCD.Input

/-- Pure extended-GCD output. -/
abbrev Output :=
  ClassicalAlgorithms.NumberTheory.XGCD.Output

/-- Pure extended-GCD state. -/
abbrev State :=
  ClassicalAlgorithms.NumberTheory.XGCD.State

/-- One pure extended-GCD transition. -/
abbrev step :=
  ClassicalAlgorithms.NumberTheory.XGCD.step

/-- The bounded pure extended-GCD execution. -/
abbrev run :=
  ClassicalAlgorithms.NumberTheory.XGCD.run

/-- The pure extended-GCD path. -/
abbrev path :=
  ClassicalAlgorithms.NumberTheory.XGCD.path

/-- The initial pure extended-GCD state. -/
abbrev initialState {width : Nat} (input : Input width) : State :=
  ClassicalAlgorithms.NumberTheory.XGCD.initialState input

/-- The final pure extended-GCD state. -/
abbrev finalState {width : Nat} (input : Input width) : State :=
  ClassicalAlgorithms.NumberTheory.XGCD.finalState input

/-- The acceptance relation for pure extended-GCD outputs. -/
abbrev accepts {width : Nat} (input : Input width) (output : Output width) :
    Prop :=
  ClassicalAlgorithms.NumberTheory.XGCD.accepts input output

/-- The deterministic pure extended-GCD evaluator. -/
abbrev eval {width : Nat} (input : Input width) : Output width :=
  ClassicalAlgorithms.NumberTheory.XGCD.eval input

/-- The coefficient width used by the pure execution. -/
abbrev executionCoefficientWidth :=
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

/-- The states visited by the pure extended-GCD execution. -/
abbrev trace {width : Nat} (input : Input width) : List State :=
  ClassicalAlgorithms.NumberTheory.XGCD.trace input

/-- The deterministic pure evaluator satisfies its acceptance relation. -/
theorem xgcdEval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) :=
  ClassicalAlgorithms.NumberTheory.XGCD.xgcdEval_accepts input

end PureXGCD

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
