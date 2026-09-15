/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Reload
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Preparation

/-!
# The actual short-DLP bank and its reusable clean seed

The complete source layout has the existing two exponent words and exactly
the power and shared arithmetic auxiliary words. Its computational-basis
preparation uses the same seed as the verified literal X reload program.
An outer runtime circuit may prepare this bank once; later rounds use the
actual reset and reload operations on these same systems.

These definitions replace no execution with a preparation descriptor. The
preparation below is the existing native BasisPreparation consumed by the
single Circuit.prepare constructor. No borrowed workspace, width rounding or
additional system is introduced.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- The existing short-DLP physical layout with each actual wire's dimension recorded. -/
def runtimeLayout (m ell width : Nat) :
    QuantumLayout (totalQubits (registerParameters m ell width)) :=
  (ShortDLP.layout (registerParameters m ell width)).toQuantumLayout

/-- One native basis preparation of the source seed in the actual ordered wire coordinates. -/
def seedPreparation (m ell width N : Nat) : BasisPreparation (runtimeLayout m ell width) :=
  ⟨(ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm
    (reloadLabel m ell width N)⟩

/-- All actual systems in the bank are qubits. -/
theorem shortDLP_runtimeLayout_dimension (m ell width : Nat)
    (wire : Fin (totalQubits (registerParameters m ell width))) :
    ((runtimeLayout m ell width).wire wire).dimension = 2 := rfl

/-- The original ordered physical identities are used without an extra system. -/
theorem shortDLP_runtimeLayout_identities (m ell width : Nat) :
    (runtimeLayout m ell width).identities =
      List.range (totalQubits (registerParameters m ell width)) :=
  (ShortDLP.layout (registerParameters m ell width)).toQuantumLayout_identities.trans
    (ShortDLP.layout_systemIdx (registerParameters m ell width))

/-- The native basis preparation is exactly the source seed in the binary carrier. -/
theorem shortDLP_seedPreparation_entry (m ell width N : Nat)
    (basis : (runtimeLayout m ell width).register.Index) :
    (seedPreparation m ell width N).normalized basis =
      NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width)))
        (reloadLabel m ell width N)
        ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis) := by
  classical
  have prepared := NormalizedVector.ket_apply (R := (runtimeLayout m ell width).register)
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm
      (reloadLabel m ell width N)) basis
  have binary := NormalizedVector.ket_apply
    (R := Qubits (totalQubits (registerParameters m ell width)))
    (reloadLabel m ell width N)
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis)
  refine prepared.trans (Eq.trans ?_ binary.symm)
  split <;> split
  · rfl
  · rename_i sourceEqual binaryDifferent
    apply False.elim
    apply binaryDifferent
    exact (congrArg (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv
      sourceEqual).trans
        ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.apply_symm_apply _)
  · rename_i sourceDifferent binaryEqual
    apply False.elim
    apply sourceDifferent
    apply (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.injective
    exact binaryEqual.trans
      ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.apply_symm_apply _).symm
  · rfl

/-- The same actual X reload used between rounds reconstructs the native preparation's seed. -/
theorem shortDLP_reload_preparation_entry (m ell width N : Nat)
    (basis : (runtimeLayout m ell width).register.Index) :
    (reloadProgram m ell width N).applyNormalized
      (NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width))) 0)
      ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis) =
        (seedPreparation m ell width N).normalized basis := by
  exact (congrArg (fun vector : NormalizedVector
      (Qubits (totalQubits (registerParameters m ell width))) =>
        vector ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv basis))
    (shortDLP_reload_apply_zero m ell width N)).trans
      (shortDLP_seedPreparation_entry m ell width N basis).symm

/-- The independently declared native preparation event is charged once when allocated. -/
theorem shortDLP_seedPreparation_eventCost (m ell width N : Nat) :
    (seedPreparation m ell width N).eventCost =
      ResourcePool.singleton (seedPreparation m ell width N).event := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU
