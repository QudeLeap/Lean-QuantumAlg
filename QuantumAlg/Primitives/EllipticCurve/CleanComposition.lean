/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.CleanInterface

/-!
# Clean composition for elliptic-curve circuit endpoints

This module packages the clean-work-register composition pattern used by
elliptic-curve point-operation stacks.  It is generic over the data and work
register labels; elliptic-curve modules instantiate it with point-operation
endpoints.  The clean-work convention reflects the source accounting rule that
auxiliary qubits for the elliptic-curve modular-arithmetic circuits are returned
to their original states [RNSL17, ECDLP.tex:555,657-684].
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

namespace CleanComposition

variable {Data Work : Type}

/-- Sequentially compose a list of clean reversible maps, starting from the
identity map.  The list order is execution order. -/
def composeList (Data Work : Type)
    (steps : List (WorkRegister.CleanReversibleMap Data Work)) :
    WorkRegister.CleanReversibleMap Data Work :=
  steps.foldl WorkRegister.CleanReversibleMap.sequential
    (WorkRegister.CleanReversibleMap.identity Data Work)

/-- The composed clean map preserves the work-register label. -/
theorem composeList_preserves_work
    (steps : List (WorkRegister.CleanReversibleMap Data Work)) (x : Data × Work) :
    ((composeList Data Work steps).perm x).2 = x.2 :=
  (composeList Data Work steps).preservesWork x

/-- Typed circuit wrapper for a composed clean map. -/
noncomputable def composedCircuit
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (steps : List (WorkRegister.CleanReversibleMap Data Work))
    (profile : ModularArithmeticResourceProfile) :
    Circuit (WorkRegister.CleanReversibleMap.register Data Work) :=
  (composeList Data Work steps).circuit profile

/-- Basis-state correctness for the composed clean circuit. -/
theorem composedCircuit_apply_ket
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (steps : List (WorkRegister.CleanReversibleMap Data Work))
    (profile : ModularArithmeticResourceProfile) (x : Data × Work) :
    Circuit.apply (composedCircuit steps profile)
      (PureState.ket (R := WorkRegister.CleanReversibleMap.register Data Work) x :
        StateVector (WorkRegister.CleanReversibleMap.register Data Work)) =
      (PureState.ket (R := WorkRegister.CleanReversibleMap.register Data Work)
        ((composeList Data Work steps).perm x) :
        StateVector (WorkRegister.CleanReversibleMap.register Data Work)) := by
  simpa [composedCircuit] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := composeList Data Work steps) (profile := profile) (x := x)

/-- The composed clean circuit keeps the work-register label clean. -/
theorem composedCircuit_preserves_work
    (steps : List (WorkRegister.CleanReversibleMap Data Work))
    (_profile : ModularArithmeticResourceProfile) (x : Data × Work) :
    ((composeList Data Work steps).perm x).2 = x.2 :=
  composeList_preserves_work steps x

/-- Resource-correct witness for a composed clean reversible endpoint. -/
noncomputable def resourceCorrectWitness
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (steps : List (WorkRegister.CleanReversibleMap Data Work))
    (profile : ModularArithmeticResourceProfile) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register Data Work)
      (∀ x : Data × Work,
        Circuit.apply (composedCircuit steps profile)
          (PureState.ket (R := WorkRegister.CleanReversibleMap.register Data Work) x :
            StateVector (WorkRegister.CleanReversibleMap.register Data Work)) =
          (PureState.ket (R := WorkRegister.CleanReversibleMap.register Data Work)
            ((composeList Data Work steps).perm x) :
            StateVector (WorkRegister.CleanReversibleMap.register Data Work)))
      ((composedCircuit steps profile).resources = profile.toResourceProfile ∧
        (composedCircuit steps profile).depth = profile.circuitDepth ∧
        (composedCircuit steps profile).queryDepth = profile.oracleQueries) := by
  exact
    { circuit := composedCircuit steps profile
      correctness := fun x => composedCircuit_apply_ket steps profile x
      resources := ⟨rfl, rfl, rfl⟩ }

end CleanComposition

end EllipticCurve
end QuantumAlg
