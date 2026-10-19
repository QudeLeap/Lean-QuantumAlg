/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Components.Classical.Model.BitWord

/-!
# The stored Shor base selects a granted member on the actual declared bank

One fixed width declaration grants every ordinary XOR member; its interpreter
supplies the public modulus. The complete
runtime parameter selects its stored base; even moduli, nonunit stored words
and every target basis value remain in the model's domain. Equal-wire transport
preserves the actual native peripherals and sole granted query.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

noncomputable section

/-- All runtime bases share the original selected BitWord execution model. -/
abbrev executionModel (N : Nat) : ExecutionModel :=
  .quantum AlgorithmGate.model
    (DeclaredSource.model (modulusBits N) (phaseBits N)) BitWord.model .empty

/-- The public modulus determines the semantics of the fixed stored-base query interface. -/
def environment {N : Nat} (input : Input N) : (executionModel N).Environment :=
  ⟨DeclaredSource.interpretation (sourceBounds input) (phaseBits N), ()⟩

/-- An empty classical service leaves only the admitted quantum interpretation. -/
lemma environment_eq_of_quantum {N : Nat} (input : Input N)
    (actual : (executionModel N).Environment)
    (same : actual.quantum = DeclaredSource.interpretation (sourceBounds input) (phaseBits N)) :
    actual = environment input := by
  cases actual with
  | mk quantum classical =>
      cases same
      cases classical
      rfl

/-- Read the already computed base without accepting a separate execution witness. -/
def selectedBase {N : Nat} (parameter : (ParameterShape (modulusBits N)).Value) :
    Fin (2 ^ modulusBits N) :=
  ⟨parameter.first.toNat, parameter.first.toNat_lt⟩

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (layout N).wires)

include sameWires in
private lemma memberWires : (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

include sameWires in
/-- The complete granted member acts on exactly the bank's current physical wires. -/
def member (parameter : (ParameterShape (modulusBits N)).Value) :
    UnitaryCircuit AlgorithmGate.model
      (DeclaredSource.model (modulusBits N) (phaseBits N)) ctx.quantumLayout :=
  Execution.unitaryOfEqualWires (layout N) ctx.quantumLayout (memberWires N sameWires)
    (DeclaredSource.circuit (modulusBits N) (phaseBits N) (selectedBase parameter))

/-- Placement retains the selected modulus/base operator on arbitrary target words. -/
lemma member_matrix
    (interpretation : (DeclaredSource.model (modulusBits N) (phaseBits N)).Interpretation)
    (parameter : (ParameterShape (modulusBits N)).Value) :
    (member N sameWires parameter).matrix interpretation =
      UnitaryOperator.reindex
        (Execution.basisOfEqualWires (layout N) ctx.quantumLayout (memberWires N sameWires))
        ((DeclaredSource.circuit (modulusBits N) (phaseBits N)
          (selectedBase parameter)).matrix interpretation) :=
  Execution.unitaryOfEqualWires_matrix (layout N) ctx.quantumLayout
    (memberWires N sameWires) interpretation _

/-- Equal-wire transport preserves every actual native event. -/
lemma member_eventCost
    (parameter : (ParameterShape (modulusBits N)).Value) :
    (member N sameWires parameter).eventCost BitWord.model .empty =
      (DeclaredSource.circuit (modulusBits N) (phaseBits N)
        (selectedBase parameter)).eventCost BitWord.model .empty :=
  Execution.unitaryOfEqualWires_cost (layout N) ctx.quantumLayout
    (memberWires N sameWires) _ BitWord.model .empty

/-- The actual placed word has one ordinary modular-exponentiation query for every stored base. -/
lemma member_queryCount
    (parameter : (ParameterShape (modulusBits N)).Value) :
    ResourcePool.count (model := executionModel N) (.oracle .modularExponentiation)
      ((member N sameWires parameter).eventCost BitWord.model .empty) = 1 := by
  rw [member_eventCost]
  exact DeclaredSource.circuit_queryCount (modulusBits N) (phaseBits N)
    (selectedBase parameter) BitWord.model .empty

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
