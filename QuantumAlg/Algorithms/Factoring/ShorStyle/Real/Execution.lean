/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Protocol
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Events
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete Shor factoring for arbitrary real failure targets

One actual machine supplies original factoring success, every full joint
output/reference fiber, borrowed restoration and all event, space and depth
obligations. Initialization and every reused round belong to the same code.
Unknown distinct primes are theorem-side data, never executable inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.RealTarget

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- The full live output context at the real-target repetition count. -/
public def post (N : Nat)
    (η : Real) : RuntimeCtx .quantum :=
  Machine.context pre pre_quantumWires N (Machine.RealTarget.repetitionCount N η)

/-- The actual source-calibrated execution initializes, samples, recovers, resets and packs once. -/
public def algorithm (N : Nat) (input : Canonical.Input N)
    (η : Real) :
    Algorithm (ShorStyle.executionModel N) pre (post N η) (OutputShape N) :=
  Machine.RealTarget.algorithm pre pre_quantumWires N input η

end

end QuantumAlg.Factoring.ShorStyle.RealTarget
