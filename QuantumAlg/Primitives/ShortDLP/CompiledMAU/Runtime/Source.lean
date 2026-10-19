/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Reload
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero

/-!
# The actual short-DLP bank and its reusable clean seed

The complete source layout contains the existing two exponent words, power
word and shared arithmetic auxiliary. Its normalized seed is a mathematical
target. The literal X reload program constructs that target from wirewise
zero; allocating and zeroing the bank are separate actual operations.

An outer runtime may allocate the bank once and retain these same physical
systems for later reset and reload. No borrowed workspace, width rounding or
additional system is introduced.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- The existing short-DLP physical layout with each actual wire's dimension recorded. -/
abbrev runtimeLayout (m ell width : Nat) :
    QuantumLayout (totalQubits (registerParameters m ell width)) :=
  (QubitLayout.canonical (totalQubits (registerParameters m ell width))).toQuantum

/-- The native layout is exactly the complete source layout, including every ordered wire. -/
lemma shortDLP_runtimeLayout_eq_source (m ell width : Nat) :
    runtimeLayout m ell width =
      (ShortDLP.layout (registerParameters m ell width)).toQuantumLayout := rfl

/-- The mathematical source seed in the actual ordered physical coordinates. -/
def seedState (m ell width N : Nat) : NormalizedVector (runtimeLayout m ell width).register :=
  NormalizedVector.ket
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm
      (reloadLabel m ell width N))

/-- All actual systems in the bank are qubits. -/
lemma shortDLP_runtimeLayout_dimension (m ell width : Nat)
    (wire : Fin (totalQubits (registerParameters m ell width))) :
    ((runtimeLayout m ell width).wire wire).dimension = 2 := rfl

/-- The original ordered physical identities are used without an extra system. -/
lemma shortDLP_runtimeLayout_identities (m ell width : Nat) :
    (runtimeLayout m ell width).identities =
      List.range (totalQubits (registerParameters m ell width)) :=
  (ShortDLP.layout (registerParameters m ell width)).toQuantumLayout_identities.trans
    (ShortDLP.layout_systemIdx (registerParameters m ell width))

/-- Binary zero denotes exactly the wirewise zero produced by actual allocation. -/
lemma shortDLP_runtimeLayout_zeroBasis (m ell width : Nat) :
    (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm 0 =
      (runtimeLayout m ell width).zeroLabel :=
  BinaryBasis.bigEndianEquiv_symm_zero _

/-- The physical seed target has exactly the source's binary basis amplitudes. -/
lemma shortDLP_seedState_entry (m ell width N : Nat)
    (basis : (runtimeLayout m ell width).register.Index) :
    seedState m ell width N basis =
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

/-- The literal X word constructs the seed from the actual allocated zero state. -/
lemma shortDLP_reload_seedState (m ell width N : Nat) :
    (reloadProgram m ell width N).applyNormalized environment
        (ZeroPreparation.normalized (runtimeLayout m ell width)) =
      seedState m ell width N := by
  change (reloadProgram m ell width N).applyNormalized environment
      (NormalizedVector.ket (runtimeLayout m ell width).zeroLabel) = _
  rw [← shortDLP_runtimeLayout_zeroBasis]
  exact shortDLP_reload_apply_zero (environment := environment) m ell width N

/-- Selecting classical operations and services preserves the literal X loading cost. -/
lemma shortDLP_reload_eventCost_classical_context (m ell width N : Nat)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (reloadProgram m ell width N).eventCost operations services =
      reloadXCount m ell width N • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((reloadProgram m ell width N).eventCost operations services) =
      ResourcePool.count event (reloadXCount m ell width N • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services) (.gate .singleQubit))
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate => cases coordinate <;> simp [shortDLP_reload_eventCost]
  | oracle query => exact nomatch query
  | classicalOperation _ => simp
  | classicalQuery _ => simp
  | preparation _ => simp
  | measurement _ => simp

end

end QuantumAlg.ShortDLP.CompiledMAU
