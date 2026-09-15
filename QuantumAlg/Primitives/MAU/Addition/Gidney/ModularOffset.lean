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

open Nat.FixedWidth

/-- Independent all-label output with both borrowed bits returned. -/
def modularOffsetOutput {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width) : Registers width :=
  (state.1, (modularWordOutput modulus constant state.2.1, state.2.2))

/-- Three actual pivot circuits, sharing the same target and arbitrary borrowed bits. -/
def modularOffsetProgram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) : UnitaryCircuit (Qubits (encoding width).width) :=
  ((pivotProgram width (offsetFirstPivot modulus constant)).seq
    (pivotProgram width modulus)).seq (pivotProgram width (offsetLastPivot modulus constant))

/-- The actual three-pivot program realizes the independent finite modular-offset contract. -/
theorem gidneyModularOffset_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding width) (modularOffsetProgram width modulus constant)
      (modularOffsetOutput modulus constant) := by
  apply (((gidneyPivot_realizes width (offsetFirstPivot modulus constant)).seq
    (gidneyPivot_realizes width modulus)).seq
      (gidneyPivot_realizes width (offsetLastPivot modulus constant))).congrStep
  rintro ⟨flag, input, helper⟩
  exact congrArg (fun word => (flag, (word, helper)))
    (gidneyModularWord_three_pivots modulus constant input)

/-- The same physical word and two borrowed bits serve every pivot. -/
theorem gidneyModularOffset_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).physical_idx = List.range (width + 2) := by
  change (pivotProgram width (offsetFirstPivot modulus constant)).physical_idx ∪
      (pivotProgram width modulus).physical_idx ∪
        (pivotProgram width (offsetLastPivot modulus constant)).physical_idx = _
  have hunion : List.range (width + 2) ∪ List.range (width + 2) = List.range (width + 2) :=
    List.Subset.union_eq_right (fun _ h => h)
  simp only [gidneyPivot_physical, hunion]

/-- The native ledger is the sum of the three actual pivot ledgers. -/
theorem gidneyModularOffset_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost =
      (pivotProgram width (offsetFirstPivot modulus constant)).eventCost +
        (pivotProgram width modulus).eventCost +
          (pivotProgram width (offsetLastPivot modulus constant)).eventCost := by
  simp only [modularOffsetProgram, UnitaryCircuit.seq_eventCost]

/-- On the original canonical domain, the accepted result is ordinary modular addition. -/
theorem gidneyModularOffset_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width)
    (hvalid : state.2.1.val < modulus.val) :
    (modularOffsetOutput modulus constant state).2.1.val =
      (state.2.1.val + constant.val) % modulus.val :=
  gidneyModularWord_valid modulus constant state.2.1 hvalid

/-- Noncanonical binary labels are fixed, along with both arbitrary borrowed bits. -/
theorem gidneyModularOffset_outside {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width)
    (houtside : modulus.val ≤ state.2.1.val) :
    modularOffsetOutput modulus constant state = state := by
  rcases state with ⟨flag, input, helper⟩
  exact congrArg (fun word => (flag, (word, helper)))
    (gidneyModularWord_outside modulus constant input houtside)

/-- An arbitrary encoded external reference is preserved jointly with the complete output. -/
theorem gidneyModularOffset_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (UnitaryCircuit.prodLeft (n := reference.width) (modularOffsetProgram width modulus constant))
      (fun state => (modularOffsetOutput modulus constant state.1, state.2)) :=
  (gidneyModularOffset_realizes width modulus constant).prodLeft

end

end QuantumAlg.MAU.Addition.Gidney
