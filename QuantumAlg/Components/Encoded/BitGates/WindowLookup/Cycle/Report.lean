/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Resources

/-!
# Separate CNOT and native-classical reporting for static-table cycles

Both quantities project the same actual event pool, using different original
coordinates. The bounds are not exact counts and imply no quantum/classical
exchange rate. These formulas cover the static-table primitive; runtime-table
AND/XOR feedback has its own separately charged native-classical bound.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

/-- Independent quantum CNOT ceiling for the actual static load/unlookup pair. -/
def staticCycleCnotLimit (wordWidth highRemaining lowWidth : Nat) : Nat :=
  (2 * (2 ^ (highRemaining + lowWidth) - 1) +
    2 * 2 ^ (highRemaining + lowWidth) * (2 * wordWidth - 1)) +
      (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2))

/-- Independent native-classical ceiling of the static selected-bit parity primitive. -/
def staticCycleClassicalLimit (wordWidth highRemaining lowWidth : Nat) : Nat :=
  1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (wordWidth + 1)

/-- The full sixteen-bit static primitive reports its two actual coordinates separately. -/
lemma staticCycle_full16_limits :
    staticCycleCnotLimit 256 7 8 = 33686010 ∧
      staticCycleClassicalLimit 256 7 8 = 16842753 := by
  norm_num [staticCycleCnotLimit, staticCycleClassicalLimit]

/-- The four-bit tail primitive has the same separate-coordinate interpretation. -/
lemma staticCycle_tail4_limits :
    staticCycleCnotLimit 256 1 2 = 8226 ∧
      staticCycleClassicalLimit 256 1 2 = 4113 := by
  norm_num [staticCycleCnotLimit, staticCycleClassicalLimit]

namespace UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

/-- Both inequalities concern the same actual path and pool, without combining the coordinates. -/
lemma cycleCircuit_separate_coordinates
    (frame : UnlookupFrame encoding wordWidth lowWidth highRemaining)
    (lookup : SelectorFrame encoding (highRemaining + lowWidth))
    (outsideAddress : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.address index).wire)
    (outsideStack : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.stack index).wire)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ wordWidth))
    (height : Nat) (output : Fin wordWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits wordWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (covered : wordWidth ≤ 2 ^ height)
    (path : (frame.cycleCircuit (services := services) lookup outsideAddress outsideStack
      physical sameWires table height output mask parity).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((frame.cycleCircuit lookup outsideAddress outsideStack physical sameWires table height
        output mask parity).resourcePool path) ≤
          staticCycleCnotLimit wordWidth highRemaining lowWidth ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.cycleCircuit lookup outsideAddress outsideStack physical sameWires table height
        output mask parity).resourcePool path) ≤
          staticCycleClassicalLimit wordWidth highRemaining lowWidth :=
  ⟨frame.cycleCircuit_cnot_count_le lookup outsideAddress outsideStack physical sameWires
      table height output mask parity covered path,
    frame.cycleCircuit_classical_weight_le lookup outsideAddress outsideStack physical sameWires
      table height output mask parity path⟩

end

end UnlookupFrame

end QuantumAlg.EncodedBit.WindowLookup
