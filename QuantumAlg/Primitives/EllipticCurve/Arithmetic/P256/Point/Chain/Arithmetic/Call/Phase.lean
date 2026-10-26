/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase.Boundary
import all QuantumAlg.Components.Encoded.BitGates.Realization.Phase
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# Exact physical character through the retained address and numerical swap

The coefficient comes from the actual paid phase program. The complete
address suffix is untouched, and the same actual three CNOT layers then
exchange the two numerical payloads on both selector branches.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

lemma suffixPhase_applyVec_of_flags (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw) (outcome : Word)
    (reset : phasePorts.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout phasePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout phasePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout phasePorts).grouping state.1).1.2.2 = false)
    (admitted : (Phase.physicalSelector selection).get state.1 = true →
      Canonical (phasePorts.source.value state.1)) :
    (Window.suffixProgram (Phase.program phasePorts selection outcome)).applyVec environment
      (Window.ket state).vec =
      WalshHadamard.walshSign outcome
        (Save.savedWord (phasePorts.source.value state.1) (phasePorts.multiplier.value state.1)
          ((Phase.physicalSelector selection).get state.1)) • (Window.ket state).vec :=
  UnitaryCircuit.Realizes.onBinaryPrefix_applyVec_encoded_ket_of_smul Frame.encoding
    Window.addressEncoding (Phase.program phasePorts selection outcome) state.1 state.1 state.2
    _ (Phase.program_applyVec_of_flags phasePorts selection environment state.1 outcome reset
      flags admitted)

/-- The paid same-mask phase and unconditional real swap retain their exact complex coefficient. -/
lemma phaseThenSwap_applyVec (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw) (outcome : Word)
    (reset : phasePorts.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout phasePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout phasePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout phasePorts).grouping state.1).1.2.2 = false)
    (admitted : (Phase.physicalSelector selection).get state.1 = true →
      Canonical (phasePorts.source.value state.1)) :
    ((Window.suffixProgram (Phase.program phasePorts selection outcome)).seq Swap.program).applyVec
        environment (Window.ket state).vec =
      WalshHadamard.walshSign outcome
        (Save.savedWord (phasePorts.source.value state.1) (phasePorts.multiplier.value state.1)
          ((Phase.physicalSelector selection).get state.1)) •
            (Window.ket (Swap.step state)).vec := by
  rw [UnitaryCircuit.applyVec_seq,
    suffixPhase_applyVec_of_flags selection environment state outcome reset flags admitted,
    UnitaryCircuit.applyVec_smul]
  have initialKet : Swap.ket state = Window.ket state := rfl
  have finalKet : Swap.ket (Swap.step state) = Window.ket (Swap.step state) := rfl
  have swapped := (congrArg (Swap.program.applyNormalized environment) initialKet).symm.trans
    ((Swap.program_apply environment state).trans finalKet)
  have vector := congrArg (fun value : NormalizedVector
    (QubitLayout.canonical Window.encoding.width).toQuantum.register => value.vec) swapped
  change Swap.program.applyVec environment (Window.ket state).vec =
    (Window.ket (Swap.step state)).vec at vector
  exact congrArg (fun value => WalshHadamard.walshSign outcome
    (Save.savedWord (phasePorts.source.value state.1) (phasePorts.multiplier.value state.1)
      ((Phase.physicalSelector selection).get state.1)) • value) vector

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
