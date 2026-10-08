/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
public import QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Representation-independent finite-group power scan

The candidate remains a native word because it is an integer modulo the known
order. The group accumulator remains in the classical oracle's hidden state.
An explicit reset starts every exponentiation; square and selected generator
multiplication are declared queries; equality writes the only visible result.
No group element is allocated in caller storage.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- The one-bit query port reused for acknowledgements and the final result. -/
@[expose, implicit_reducible] public def serviceInput
    (result : CWriteRef ctx .bit) : CInputRef ctx .bit :=
  .storage result.toCStorageRef

/-- Explicitly reset the hidden accumulator to the group identity. -/
@[expose, implicit_reducible] public def resetQuery (result : CWriteRef ctx .bit) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .classicalQuery
    { query := .reset
      input := serviceInput result
      output := result }

/-- One declared group operation squares the hidden accumulator. -/
@[expose, implicit_reducible] public def squareQuery (result : CWriteRef ctx .bit) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .classicalQuery
    { query := .square
      input := serviceInput result
      output := result }

/-- One declaration-owned generator multiplication updates the hidden accumulator. -/
@[expose, implicit_reducible] public def multiplyGeneratorQuery (result : CWriteRef ctx .bit) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .classicalQuery
    { query := ClassicalFiniteGroupOracle.multiplyRightQuery G P.generator
      input := serviceInput result
      output := result }

/-- One stored candidate bit either performs the granted multiplication or
leaves the accumulator unchanged. -/
@[expose, implicit_reducible] public def multiplyChoice (result : CWriteRef ctx .bit)
    (value : CShape.Value .bit) : Circuit (OrderExecution.model P) ctx ctx :=
  match value with
  | .bit false => .id (model := OrderExecution.model P) ctx
  | .bit true => multiplyGeneratorQuery P result

/-- One big-endian exponentiation step squares before the selected multiply. -/
@[expose, implicit_reducible] public def powerStep
    (bit : CInputRef ctx .bit) (result : CWriteRef ctx .bit) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .seq (squareQuery P result) (.branch bit (multiplyChoice P result))

/-- Scan every actual candidate bit from most significant to least significant. -/
@[expose, implicit_reducible] public def powerScan {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width))
    (result : CWriteRef ctx .bit) : Circuit (OrderExecution.model P) ctx ctx :=
  Circuit.forRange width fun index =>
    powerStep P (.wordBitGet candidate index) result

/-- Compare the hidden accumulator with the problem target. -/
@[expose, implicit_reducible] public def targetEqualityQuery (result : CWriteRef ctx .bit) :
    Circuit (OrderExecution.model P) ctx ctx :=
  .classicalQuery
    { query := ClassicalFiniteGroupOracle.equalsQuery G P.target
      input := serviceInput result
      output := result }

/-- Explicit reset, complete power scan and target comparison. -/
@[expose, implicit_reducible] public def powerCheck {width : Nat}
    (candidate : CInputRef ctx (.unsignedWord width))
    (result : CWriteRef ctx .bit) : Circuit (OrderExecution.model P) ctx ctx :=
  .seq (resetQuery P result)
    (.seq (powerScan P candidate result) (targetEqualityQuery P result))

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
