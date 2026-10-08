/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Final
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Seed

/-!
# Finite-cyclic discrete logarithms

The public problem and algorithm use the same complete fresh-bank execution.
Every positive group order is supported, including order one and powers of two.
Group systems keep their native dimension; neither quantum nor classical group
access invents a bit encoding for them.
-/

namespace QuantumAlg.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The known-order finite-cyclic discrete-logarithm problem. The secret is a
proof-side witness in the acceptance relation and never an executable input. -/
public def problem (P : KnownOrderProblem G) (input : Input P) :
    Problem (OrderExecution.model P) OrderExecution.pre (OrderEndpoint.outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  OrderEndpoint.problem P input

/-- Fresh native-dimensional sample banks followed by checked first-success recovery. -/
@[expose] public def algorithm (P : KnownOrderProblem G) :
    Algorithm (OrderExecution.model P) OrderExecution.pre (OrderEndpoint.outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  OrderEndpoint.algorithm P

/-- The complete execution returns the advertised discrete logarithm with
probability at least two thirds and meets its independent native budgets. -/
public theorem main (P : KnownOrderProblem G) (input : Input P) :
    Algorithm.Solves (algorithm P) (problem P input) :=
  OrderEndpoint.algorithm_solves P input

end

end QuantumAlg.FiniteCyclicDLP
