/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Coherent

/-!
# Actual chronological MAC common scalar on arbitrary original source/reference data

Every selected measured row uses the original shared bank and the actual
Store produced by preceding rows. Its two helpers are physically clean at
that input. The product scalar depends only on the static constant bank,
including literal zero rows, and not on source, dirty, control, flag or
reference amplitudes [G25, main.tex:199-295,271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Only the two original measured-adder helpers are initialized for the MAC record law. -/
def helpersClean (layout : Layout encoding width) (state : Data) : Prop :=
  ∀ helper, (layout.clean helper).get state = false

/-- The input-independent scalar product follows the same actual increasing-source prefix. -/
def accumulatePrefixAlpha (constants : Fin width → BitVec width) :
    (count : Nat) → count ≤ width → ℂ
  | 0, _ => 1
  | count + 1, bounded =>
      accumulatePrefixAlpha constants count (by omega) *
        (if constants ⟨count, by omega⟩ = 0 then 1 else
          NormalizedVector.invSqrt2 ^ (2 * (width - 2)))

/-- All actual prefix records act with one scalar on the complete clean-helper input subspace. -/
lemma accumulatePrefixWord_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment
        (layout.accumulatePrefixWord wide modulus constants count bounded)
        (accumulatePrefixAlpha constants count bounded) layout.helpersClean := by
  induction count with
  | zero =>
      exact recordCoherent_nil physical sameWires bank.output environment layout.helpersClean
  | succ count ih =>
      rw [accumulatePrefixWord, accumulatePrefixAlpha]
      have earlier := ih (by omega)
      have row := Addition.Gidney.Measured.Reduction.Layout.modularWord_recordCoherent
        (operations := operations) (services := services) (layout.reductionLayout ⟨count, by omega⟩)
        wide modulus (constants ⟨count, by omega⟩) physical sameWires bank environment
      exact recordCoherent_append physical sameWires bank.output environment _ _ _ _
        layout.helpersClean layout.helpersClean earlier row
        (fun state clean =>
          (accumulatePrefixWord_frame layout wide modulus constants count (by omega)
            state clean).clean)

/-- The actual forward MAC preserves arbitrary joint data/reference amplitudes on every record. -/
lemma forwardMACWord_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment (layout.forwardMACWord wide modulus coefficient)
        (accumulatePrefixAlpha (forwardConstant modulus coefficient) width le_rfl)
          layout.helpersClean :=
  accumulatePrefixWord_recordCoherent layout wide modulus _ width le_rfl
    physical sameWires bank environment

/-- The separately emitted negative MAC has its own actual common-scalar record law. -/
lemma inverseMACWord_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient : Nat) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment (layout.inverseMACWord wide modulus coefficient)
        (accumulatePrefixAlpha (inverseConstant modulus coefficient) width le_rfl)
          layout.helpersClean :=
  accumulatePrefixWord_recordCoherent layout wide modulus _ width le_rfl
    physical sameWires bank environment

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
