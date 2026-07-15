/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Core.EncodedBasisMap

/-!
# Clean-ancilla interface for modular arithmetic units

This module turns a work-preserving reversible map into the shared typed-circuit
interface used by modular-arithmetic units.  The same `Circuit` object carries
the basis-map correctness statement and the projected resource profile, so
downstream arithmetic components do not need separate correctness and resource
witnesses.
-/

@[expose] public section

namespace QuantumAlg

namespace ModularArithmetic

/-- Data and target labels are bundled before attaching the reusable work
register.  Concrete arithmetic units decide what belongs in each component. -/
abbrev DataTarget (Data Target : Type) :=
  Data × Target

/-- Clean-ancilla reversible map with separate data, target, and work labels. -/
abbrev CleanAncillaMap (Data Target Work : Type) :=
  WorkRegister.CleanReversibleMap (DataTarget Data Target) Work

end ModularArithmetic

namespace WorkRegister

namespace CleanReversibleMap

variable {Data Work : Type}

/-- Register whose basis labels are data/work pairs for a clean reversible map. -/
def register (Data Work : Type)
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work] :
    Register where
  Index := Data × Work
  fintype := inferInstance
  decEq := inferInstance

/-- Permutation gate induced by a clean reversible map. -/
noncomputable def gate [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work) : Gate (register Data Work) :=
  Gate.ofPerm clean.perm.symm

/-- Basis-state action of the clean reversible map gate. -/
theorem gate_apply_ket [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work) (x : Data × Work) :
    clean.gate.apply (PureState.ket (R := register Data Work) x) =
      PureState.ket (R := register Data Work) (clean.perm x) := by
  rw [gate, Gate.ofPerm_apply_ket]
  rfl

/-- Typed circuit wrapper induced by a clean reversible map and a modular
arithmetic resource profile. -/
noncomputable def circuit
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) : Circuit (register Data Work) :=
  Circuit.ofGate "clean-ancilla-reversible-map" clean.gate profile.toResourceProfile
    profile.circuitDepth profile.oracleQueries

@[simp] theorem circuit_resources
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) :
    (clean.circuit profile).resources = profile.toResourceProfile :=
  rfl

@[simp] theorem circuit_depth
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) :
    (clean.circuit profile).depth = profile.circuitDepth :=
  rfl

@[simp] theorem circuit_queryDepth
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) :
    (clean.circuit profile).queryDepth = profile.oracleQueries :=
  rfl

/-- Basis-state action of the typed clean reversible circuit. -/
theorem circuit_apply_ket
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) (x : Data × Work) :
    Circuit.apply (clean.circuit profile)
      (PureState.ket (R := register Data Work) x : StateVector (register Data Work)) =
      (PureState.ket (R := register Data Work) (clean.perm x) :
        StateVector (register Data Work)) := by
  simpa [circuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register Data Work) =>
      (psi : StateVector (register Data Work))) (gate_apply_ket clean x)

/-- The clean reversible circuit preserves the work-register label on every
basis input. -/
private theorem circuit_preserves_work
    (clean : CleanReversibleMap Data Work)
    (_profile : ModularArithmeticResourceProfile) (x : Data × Work) :
    (clean.perm x).2 = x.2 :=
  clean.preservesWork x

/-- Resource-correct witness for the clean reversible circuit wrapper:
correctness and resource counters refer to the same typed `Circuit`. -/
noncomputable def resourceCorrectWitness
    [Fintype Data] [DecidableEq Data] [Fintype Work] [DecidableEq Work]
    (clean : CleanReversibleMap Data Work)
    (profile : ModularArithmeticResourceProfile) :
    ResourceCorrectWitness (R := register Data Work)
      (∀ x : Data × Work,
        Circuit.apply (clean.circuit profile)
          (PureState.ket (R := register Data Work) x :
            StateVector (register Data Work)) =
          (PureState.ket (R := register Data Work) (clean.perm x) :
            StateVector (register Data Work)))
      ((clean.circuit profile).resources = profile.toResourceProfile ∧
        (clean.circuit profile).depth = profile.circuitDepth ∧
        (clean.circuit profile).queryDepth = profile.oracleQueries) := by
  exact
    { circuit := clean.circuit profile
      correctness := fun x => circuit_apply_ket clean profile x
      resources := ⟨rfl, rfl, rfl⟩ }

end CleanReversibleMap

end WorkRegister

end QuantumAlg
