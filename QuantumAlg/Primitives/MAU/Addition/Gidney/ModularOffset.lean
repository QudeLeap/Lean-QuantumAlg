/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.PivotFlip

/-!
# Actual three-pivot modular constant offset

The executed pivots are `modulus - constant`, `modulus`, and `constant`
[G17, paper.tex:319-334]. Each pivot restores both arbitrary borrowed
bits. The exact word output is independently specified by modular addition
on canonical residues and identity on the remaining labels. Modulus one,
even moduli, zero constants, and full-capacity moduli are included.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth EncodedBit GateSpec

/-- Independent all-label output with both borrowed bits returned. -/
def modularOffsetOutput {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width) : Registers width :=
  (state.1, (modularWordOutput modulus constant state.2.1, state.2.2))

/-- The three literal pivot lists share the same two arbitrary borrowed bits. -/
def modularOffsetGates (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) : List (GateSpec (encoding width)) :=
  (pivotGates width (offsetFirstPivot modulus constant) ++ pivotGates width modulus) ++
    pivotGates width (offsetLastPivot modulus constant)

/-- The actual list realizes the independent finite modular-offset contract. -/
lemma gidneyModularOffsetGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width) :
    stepList (modularOffsetGates width modulus constant) state =
      modularOffsetOutput modulus constant state := by
  simp only [modularOffsetGates, stepList_append, gidneyPivotGates_step]
  rcases state with ⟨flag, input, helper⟩
  exact congrArg (fun word => (flag, (word, helper)))
    (gidneyModularWord_three_pivots modulus constant input)

/-- Emit the three actual pivot expansions on the fixed word and two borrowed bits. -/
def modularOffsetProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (modularOffsetGates width modulus constant)

/-- The actual three-pivot program realizes the independent all-label modular offset. -/
lemma gidneyModularOffset_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding width) (modularOffsetProgram width modulus constant)
      environment
      (modularOffsetOutput modulus constant) :=
  realizesList_congrStep _ _ _ (gidneyModularOffsetGates_step width modulus constant) environment

/-- All three pivots use the same word and exactly two arbitrary borrowed bits. -/
lemma gidneyModularOffset_interface (width : Nat) (modulus : Fin (2 ^ width + 1))
    (_constant : Fin (modulus.val + 1)) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (width + 2) :=
  gidneyPivot_interface width modulus

/-- The native ledger is the sum of the three actual pivot ledgers. -/
lemma gidneyModularOffset_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost =
      (pivotProgram width (offsetFirstPivot modulus constant)).eventCost +
        (pivotProgram width modulus).eventCost +
          (pivotProgram width (offsetLastPivot modulus constant)).eventCost := by
  simp only [modularOffsetProgram, pivotProgram, programList_eventCost,
    modularOffsetGates, List.map_append, ResourcePool.ofList_append]

/-- On the original canonical domain, the accepted result is ordinary modular addition. -/
lemma gidneyModularOffset_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width)
    (hvalid : state.2.1.val < modulus.val) :
    (modularOffsetOutput modulus constant state).2.1.val =
      (state.2.1.val + constant.val) % modulus.val :=
  gidneyModularWord_valid modulus constant state.2.1 hvalid

/-- Noncanonical binary labels are fixed, along with both arbitrary borrowed bits. -/
lemma gidneyModularOffset_outside {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width)
    (houtside : modulus.val ≤ state.2.1.val) :
    modularOffsetOutput modulus constant state = state := by
  rcases state with ⟨flag, input, helper⟩
  exact congrArg (fun word => (flag, (word, helper)))
    (gidneyModularWord_outside modulus constant input houtside)

/-- An arbitrary encoded external reference is preserved jointly with the complete output. -/
lemma gidneyModularOffset_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (layout := QubitLayout.canonical ((encoding width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width (modularOffsetProgram width modulus constant))
      environment
      (fun state => (modularOffsetOutput modulus constant state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (gidneyModularOffset_realizes width modulus constant)

end

end QuantumAlg.MAU.Addition.Gidney
