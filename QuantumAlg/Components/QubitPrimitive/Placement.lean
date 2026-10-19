/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Gate.Placement.Construction

/-!
# Addressed primitives in the default native model

The primitive selects the model's X, CNOT or Toffoli instance and its original
logical arguments. An ambient qubit layout supplies their actual physical
identities. The application keeps the whole ambient layout and extends the
native action by identity on every unused wire; it accepts no separate operator.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

/-- The actual default-model token selected by the addressed primitive. -/
@[expose]
public def nativeToken {n : Nat} : QubitPrimitive n → AlgorithmGate.Token
  | .x _ => .singleQubit Gate.XOp
  | .cnot _ _ _ => .cnot
  | .toffoli _ _ _ _ _ _ => .toffoli

/-- Ordered logical argument positions, retaining control and target order. -/
@[expose]
public def nativePositions {n : Nat} : QubitPrimitive n → List (Fin n)
  | .x target => [target]
  | .cnot control target _ => [control, target]
  | .toffoli first second target _ _ _ => [first, second, target]

/-- The model-owned token is placed on the primitive's actual, distinct arguments. -/
@[expose]
public def nativeApplication {n : Nat} (layout : QubitLayout n) (primitive : QubitPrimitive n) :
    GateModel.Application AlgorithmGate.model layout.toQuantum :=
  match primitive with
  | .x target =>
      GateModel.Application.ofPositions AlgorithmGate.model (.singleQubit Gate.XOp) layout.toQuantum
        ⟨fun _ => target, fun (left right : Fin 1) _ => Subsingleton.elim left right⟩
        (fun _ => rfl)
  | .cnot control target different =>
      GateModel.Application.ofPositions AlgorithmGate.model .cnot layout.toQuantum
        ⟨![control, target], by
          intro left right same
          fin_cases left <;> fin_cases right <;> simp_all⟩ (fun _ => rfl)
  | .toffoli first second target distinct firstTarget secondTarget =>
      GateModel.Application.ofPositions AlgorithmGate.model .toffoli layout.toQuantum
        ⟨![first, second, target], by
          intro left right same
          fin_cases left <;> fin_cases right <;> simp_all⟩ (fun _ => rfl)

/-- Placement retains the model instance, including the exact X operator parameter. -/
public lemma nativeApplication_token {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    (nativeApplication layout primitive).occurrence.token = nativeToken primitive := by
  cases primitive <;> rfl

/-- The native resource coordinate follows that same actual token. -/
public lemma nativeApplication_coordinate {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    (nativeApplication layout primitive).coordinate =
      AlgorithmGate.model.coordinate (nativeToken primitive) := by
  cases primitive <;> rfl

/-- Only the addressed arguments occur in the native footprint, in their original order. -/
public lemma nativeApplication_physicalFootprint {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    (nativeApplication layout primitive).occurrence.placement.layout.identities =
      (nativePositions primitive).map layout.physical_idx := by
  cases primitive <;> rfl

end

end QuantumAlg.QubitPrimitive
