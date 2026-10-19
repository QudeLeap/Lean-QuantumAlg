/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Space
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget

/-!
# Independent native budgets for the full stored-sample factor tail

The modulus selects its original exceptional route at compilation. Stored
early-factor and order-guard branches use coordinatewise maxima of their real
continuations. All initialization, order recovery, modular half-power, GCD,
nominal decoding and result packaging are included. These width-only formulas
are independent specifications, and subsequent laws bound the actual trace.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open ClassicalRoutines

noncomputable section

/-- The five real guard operations retain their actual word widths and Boolean coordinates. -/
def guardEvents (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : List (Resource.Event
    model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .bitXor
      (phaseBits N + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .lessThan
        (phaseBits N + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Every branch returns through the same native option representation at the modulus width. -/
def packBudget (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption (modulusBits N)))))

/-- Both true half-order stages contribute their full independent native event allowance. -/
def reduceEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool
    model :=
  NativeHalfPower.eventEnvelope model N + NativeHalfFactorScope.eventEnvelope model N

/-- The genuine guard chooses reduction or a real option-none packaging instruction. -/
def checkedEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool
    model :=
  ResourcePool.ofList (guardEvents model N) +
    ResourcePool.max (packBudget model N) (reduceEnvelope model N)

/-- Real early-factor priority admits either its single pack or the full checked order route. -/
def dispatchEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool
    model :=
  ResourcePool.max (packBudget model N) (checkedEnvelope model N)

/-- Actual stored base packing, complete order recovery and its nominal decode precede dispatch. -/
def recoveredEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool
    model :=
  ResourcePool.singleton
    (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.residueEncoding .pack
        (modulusBits N)))) +
      (OrderRecovery.Native.eventEnvelope model (modulusBits N) (phaseBits N) +
        (ResourcePool.singleton
          (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.nominalEncoding
              (.unpackOption (phaseBits N + 1))))) +
          dispatchEnvelope model N))

/-- The exception executes two actual bit writes, a literal factor-two load and a real pack. -/
def evenEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .xor))) +
    (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.bit .not))) +
      (ConstantWord.envelope model (modulusBits N) + packBudget model N))

/-- The public modulus alone chooses the original exceptional or full recovery allowance. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (N : Nat) : ResourcePool model
    :=
  if 2 < N ∧ Even N then evenEnvelope model N else recoveredEnvelope model N

/-- Independent serial allowance for actual modular half-power and complete factor selection. -/
def reduceDepth (N : Nat) : Nat :=
  1 + (2 * modulusBits N + 5 + 6 * (phaseBits N + 1)) + NativeHalfFactorScope.depthBound N

/-- Actual early-factor or guarded order dispatch has this independent serial bound. -/
def dispatchDepth (N : Nat) : Nat := max 1 (5 + max 1 (reduceDepth N))

/-- The non-exceptional sequence also counts the two nominal input representation operations. -/
def recoveredDepth (N : Nat) : Nat :=
  1 + (OrderRecovery.Native.unitDepthBound (modulusBits N) (phaseBits N) +
    (1 + dispatchDepth N))

/-- The exception's two flag writes and final pack surround the actual constant load. -/
def evenDepth (N : Nat) : Nat := 3 + 2 * modulusBits N

/-- Independent unit duration keeps the same original known-modulus distinction. -/
def depthBound (N : Nat) : Nat :=
  if 2 < N ∧ Even N then evenDepth N else recoveredDepth N

/-- Actual order recovery bounds all temporary work of the sequential tail stages. -/
def spaceBound (kind : ProblemKind) (N : Nat) : SpacePool kind :=
  SpacePool.ofShape
    (.bits (OrderRecovery.Native.extraClassicalBits (modulusBits N) (phaseBits N)))

/-- The independent order-recovery capacity covers the simultaneous half-order power scratch. -/
lemma halfPower_space_le (kind : ProblemKind) (N : Nat) :
    NativeHalfPower.spaceBound kind N ≤ spaceBound kind N := by
  intro axis
  cases axis <;> simp [NativeHalfPower.spaceBound, spaceBound, SpacePool.ofShape,
    OrderRecovery.Native.extraClassicalBits]
  omega

/-- The same independent capacity also covers every live outer and inner GCD-selection cell. -/
lemma halfFactor_space_le (kind : ProblemKind) (N : Nat) :
    NativeHalfFactorScope.spaceBound kind N ≤ spaceBound kind N := by
  intro axis
  cases axis <;> simp [NativeHalfFactorScope.spaceBound, spaceBound, SpacePool.ofShape,
    OrderRecovery.Native.extraClassicalBits]
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
