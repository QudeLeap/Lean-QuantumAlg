/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Support
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Primitives.WalshHadamard

/-!
# Grover's actual elementary diffusion circuit

Only a positive iteration count at source width at least four needs the
single dirty work wire. Small widths use the work-free source reflection;
zero iterations execute only the original initial Hadamards. Every other
branch composes the original phase oracle with literal H-adjoint, elementary
positive zero reflection, H. The source and all actual work positions remain
present in the complete register.
-/

namespace QuantumAlg.GroverSearch.Elementary

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- The original initial Hadamards, with identity on the actual work suffix. -/
def hadamards (n k : Nat) : UnitaryCircuit (Qubits (totalQubits n k)) :=
  (initialPreparationCircuit n).idleSuffix
    (by simpa only [initialPreparationCircuit, WalshHadamard.hadamardLayer_physical_idx]
      using (List.Subset.refl (List.range n)))
    (helperWidth n k)

/-- One actual source phase query, with all work values untouched. -/
def oracle {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (phaseOracleCircuit marked).idleSuffix (by exact List.Subset.refl _) (helperWidth n k)

/-- The original diffusion decomposition now contains the real elementary source circuit. -/
def diffusion (n k : Nat) (nonzero : k ≠ 0) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (hadamards n k).dagger.seq ((reflection n k nonzero).seq (hadamards n k))

/-- One actual phase query followed by the actual elementary diffusion sequence. -/
def step {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) (nonzero : k ≠ 0) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (oracle marked k).seq (diffusion n k nonzero)

/-- The empty schedule needs no work; nonempty schedules retain their actual repeated body. -/
def body {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  if zero : k = 0 then hadamards n k
  else (hadamards n k).seq (UnitaryCircuit.iterate k (step marked k zero))

/-- The final structural identity gives the existing live interface its canonical physical order. -/
def circuit {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    UnitaryCircuit (Qubits (totalQubits n k)) :=
  (body marked k).seq
    (UnitaryCircuit.identity (Qubits (totalQubits n k))
      (List.range (totalQubits n k)) List.nodup_range)

theorem hadamards_contained (n k : Nat) :
    (hadamards n k).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _

theorem oracle_contained {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (oracle marked k).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.idleSuffix_physical_idx_subset_range _ _ _

theorem diffusion_contained (n k : Nat) (nonzero : k ≠ 0) :
    (diffusion n k nonzero).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.dagger_physical_idx_subset _ (hadamards_contained n k))
    (UnitaryCircuit.seq_physical_idx_subset _ _ (reflection_contained n k nonzero)
      (hadamards_contained n k))

theorem step_contained {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) (nonzero : k ≠ 0) :
    (step marked k nonzero).physical_idx ⊆ List.range (totalQubits n k) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (oracle_contained marked k)
    (diffusion_contained n k nonzero)

theorem body_contained {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (body marked k).physical_idx ⊆ List.range (totalQubits n k) := by
  unfold body
  split
  · exact hadamards_contained n k
  · exact UnitaryCircuit.seq_physical_idx_subset _ _ (hadamards_contained n k)
      (UnitaryCircuit.iterate_physical_idx_subset _ _ (step_contained marked k _))

/-- The actual complete circuit exposes every live source and work position exactly once. -/
theorem circuit_physical_idx {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).physical_idx = List.range (totalQubits n k) :=
  UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ (body_contained marked k)

end

end QuantumAlg.GroverSearch.Elementary
