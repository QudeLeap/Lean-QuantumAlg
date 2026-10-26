/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse

/-!
# Reused forward input from the actual reset and original complete source initialization

Measured multiplication saves its product before the reused forward EEA.
After physical Y reset, every source bit outside saved A must retain its
original initialized value. This is a different boundary from the
post-forward history required by the reused adjoint in division.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse

noncomputable section

/-- Complete initialized source readouts and actual Y reset identify reused forward input. -/
lemma initial_of_saved_reset (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags)
    (state : ControlledResidentFrame.Data modulus.size)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get state.1.1.1 =
        bit.get (ControlledResident.initial modulus input 0 pool flags).1.1.1)
    (poolSame : state.1.1.2 = pool) (reset : state.1.2 = 0) (flagsSame : state.2 = flags) :
    state = initial modulus input
      (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1)) pool flags := by
  have zero (index : Fin modulus.size) :
      (ControlledResident.initial modulus input 0 pool flags).1.1.1.firstWord.getMsbD
        index.val = false :=
    InitialPortProgram.inputFrame_large_bit modulus input index
  have grouped := WorkspaceReuse.grouping_saved_reset modulus.size
    (ControlledResident.initial modulus input 0 pool flags).1.1 state.1 zero retained poolSame reset
  apply (layout modulus.size).grouping.injective
  rw [initial, Equiv.apply_symm_apply]
  change ((WorkspaceReuse.placement modulus.size).grouping state.1, state.2) = _
  rw [grouped, flagsSame]
  rfl

/-- The same actual reused forward executes after saving the product and physically resetting Y. -/
lemma forward_saved_reset (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.2.1 = true)
    (state : ControlledResidentFrame.Data modulus.size)
    (retained : ∀ bit : EncodedBit (SharedEEA.encoding modulus.size),
      modulus.size ≤ bit.wire.val → bit.get state.1.1.1 =
        bit.get (ControlledResident.initial modulus input 0 pool flags).1.1.1)
    (poolSame : state.1.1.2 = pool) (reset : state.1.2 = 0) (flagsSame : state.2 = flags) :
    (forward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (result modulus input positive bounded
            (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1)) pool flags))) := by
  have same := initial_of_saved_reset modulus input pool flags state
    retained poolSame reset flagsSame
  have actual := forward_initial modulus nontrivial environment input
    (WorkspaceReuse.reverseWord (WorkspaceReuse.largeWord state.1)) coprime positive bounded
    pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun value => (forward modulus nontrivial).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledResidentFrame.encoding modulus.size).encode value)))) same).trans actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse
