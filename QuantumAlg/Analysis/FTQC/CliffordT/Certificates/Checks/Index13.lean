/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word13Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word13State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step0 :
    word13Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word13State1 := by decide +kernel

private def word13Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word13State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step1 :
    word13Chunk1.foldl (fun acc a => a.applyPacked acc)
      word13State1 = word13State2 := by decide +kernel

private def word13Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word13State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step2 :
    word13Chunk2.foldl (fun acc a => a.applyPacked acc)
      word13State2 = word13State3 := by decide +kernel

private def word13Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word13State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step3 :
    word13Chunk3.foldl (fun acc a => a.applyPacked acc)
      word13State3 = word13State4 := by decide +kernel

private def word13Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word13State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step4 :
    word13Chunk4.foldl (fun acc a => a.applyPacked acc)
      word13State4 = word13State5 := by decide +kernel

private def word13Chunk5 : List Letter := [.h, .s, .s, .s, .h, .s, .s, .h]
private def word13State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step5 :
    word13Chunk5.foldl (fun acc a => a.applyPacked acc)
      word13State5 = word13State6 := by decide +kernel

private def word13Chunk6 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word13State7 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word13Step6 :
    word13Chunk6.foldl (fun acc a => a.applyPacked acc)
      word13State6 = word13State7 := by decide +kernel

private def word13Chunk7 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word13State8 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word13Step7 :
    word13Chunk7.foldl (fun acc a => a.applyPacked acc)
      word13State7 = word13State8 := by decide +kernel

private def word13Chunk8 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word13State9 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word13Step8 :
    word13Chunk8.foldl (fun acc a => a.applyPacked acc)
      word13State8 = word13State9 := by decide +kernel

private def word13Chunk9 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word13State10 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word13Step9 :
    word13Chunk9.foldl (fun acc a => a.applyPacked acc)
      word13State9 = word13State10 := by decide +kernel

private def word13Chunk10 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word13State11 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((23 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word13Step10 :
    word13Chunk10.foldl (fun acc a => a.applyPacked acc)
      word13State10 = word13State11 := by decide +kernel

private def word13Chunk11 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word13State12 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-13 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word13Step11 :
    word13Chunk11.foldl (fun acc a => a.applyPacked acc)
      word13State11 = word13State12 := by decide +kernel

private def word13Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word13State13 : PackedMat2 :=
    ⟨⟨⟨((-17 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 7)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((39 : Dyadic) * half ^ 7)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((21 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word13Step12 :
    word13Chunk12.foldl (fun acc a => a.applyPacked acc)
      word13State12 = word13State13 := by decide +kernel

private def word13Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word13State14 : PackedMat2 :=
    ⟨⟨⟨((-67 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 8)⟩,
       ⟨((-45 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((-41 : Dyadic) * half ^ 8)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 7),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 8)⟩,
       ⟨((45 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word13Step13 :
    word13Chunk13.foldl (fun acc a => a.applyPacked acc)
      word13State13 = word13State14 := by decide +kernel

private def word13Chunk14 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word13State15 : PackedMat2 :=
    ⟨⟨⟨((-95 : Dyadic) * half ^ 8),
        ((157 : Dyadic) * half ^ 9)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((-131 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((49 : Dyadic) * half ^ 8),
        ((-123 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 8),
        ((55 : Dyadic) * half ^ 9)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((43 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 8),
        ((255 : Dyadic) * half ^ 9)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((-65 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word13Step14 :
    word13Chunk14.foldl (fun acc a => a.applyPacked acc)
      word13State14 = word13State15 := by decide +kernel

private def word13Chunk15 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word13State16 : PackedMat2 :=
    ⟨⟨⟨((69 : Dyadic) * half ^ 8),
        ((-5 : Dyadic) * half ^ 9)⟩,
       ⟨((-231 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 7),
        (0 : Dyadic)⟩,
       ⟨((51 : Dyadic) * half ^ 8),
        ((43 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 9),
        ((-11 : Dyadic) * half ^ 9)⟩,
       ⟨((43 : Dyadic) * half ^ 9),
        ((113 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 9),
        ((75 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 9),
        ((81 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word13Step15 :
    word13Chunk15.foldl (fun acc a => a.applyPacked acc)
      word13State15 = word13State16 := by decide +kernel

private def word13Chunk16 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word13State17 : PackedMat2 :=
    ⟨⟨⟨((413 : Dyadic) * half ^ 10),
        ((85 : Dyadic) * half ^ 8)⟩,
       ⟨((727 : Dyadic) * half ^ 10),
        ((-175 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((193 : Dyadic) * half ^ 10),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-73 : Dyadic) * half ^ 10),
        ((75 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((73 : Dyadic) * half ^ 10),
        ((-75 : Dyadic) * half ^ 10)⟩,
       ⟨((-193 : Dyadic) * half ^ 10),
        ((5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((727 : Dyadic) * half ^ 10),
        ((-175 : Dyadic) * half ^ 10)⟩,
       ⟨((413 : Dyadic) * half ^ 10),
        ((85 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word13Step16 :
    word13Chunk16.foldl (fun acc a => a.applyPacked acc)
      word13State16 = word13State17 := by decide +kernel

private def word13Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word13State18 : PackedMat2 :=
    ⟨⟨⟨((-165 : Dyadic) * half ^ 9),
        ((-191 : Dyadic) * half ^ 10)⟩,
       ⟨((-17 : Dyadic) * half ^ 10),
        ((119 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 10),
        ((167 : Dyadic) * half ^ 9)⟩,
       ⟨((51 : Dyadic) * half ^ 7),
        ((-53 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((57 : Dyadic) * half ^ 8),
        ((373 : Dyadic) * half ^ 11)⟩,
       ⟨((55 : Dyadic) * half ^ 7),
        ((-443 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-285 : Dyadic) * half ^ 10),
        ((347 : Dyadic) * half ^ 11)⟩,
       ⟨((667 : Dyadic) * half ^ 10),
        ((313 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word13Step17 :
    word13Chunk17.foldl (fun acc a => a.applyPacked acc)
      word13State17 = word13State18 := by decide +kernel

private def word13Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word13State19 : PackedMat2 :=
    ⟨⟨⟨((-199 : Dyadic) * half ^ 9),
        ((91 : Dyadic) * half ^ 11)⟩,
       ⟨((135 : Dyadic) * half ^ 11),
        ((11 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1097 : Dyadic) * half ^ 11),
        ((-289 : Dyadic) * half ^ 11)⟩,
       ⟨((177 : Dyadic) * half ^ 8),
        ((137 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 11),
        ((-2513 : Dyadic) * half ^ 12)⟩,
       ⟨((563 : Dyadic) * half ^ 11),
        ((319 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((51 : Dyadic) * half ^ 10),
        ((-661 : Dyadic) * half ^ 12)⟩,
       ⟨((5 : Dyadic) * half ^ 7),
        ((-931 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word13Step18 :
    word13Chunk18.foldl (fun acc a => a.applyPacked acc)
      word13State18 = word13State19 := by decide +kernel

private def word13Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word13State20 : PackedMat2 :=
    ⟨⟨⟨((31 : Dyadic) * half ^ 11),
        ((-4127 : Dyadic) * half ^ 13)⟩,
       ⟨((-211 : Dyadic) * half ^ 12),
        ((771 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-473 : Dyadic) * half ^ 10),
        ((985 : Dyadic) * half ^ 13)⟩,
       ⟨((1725 : Dyadic) * half ^ 12),
        ((1323 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-473 : Dyadic) * half ^ 10),
        ((985 : Dyadic) * half ^ 13)⟩,
       ⟨((-1725 : Dyadic) * half ^ 12),
        ((-1323 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 11),
        ((4127 : Dyadic) * half ^ 13)⟩,
       ⟨((-211 : Dyadic) * half ^ 12),
        ((771 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word13Step19 :
    word13Chunk19.foldl (fun acc a => a.applyPacked acc)
      word13State19 = word13State20 := by decide +kernel

private def word13Chunk20 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word13State21 : PackedMat2 :=
    ⟨⟨⟨((-2469 : Dyadic) * half ^ 13),
        ((3 : Dyadic) * half ^ 12)⟩,
       ⟨((-2559 : Dyadic) * half ^ 13),
        ((-305 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((2447 : Dyadic) * half ^ 13),
        ((-3099 : Dyadic) * half ^ 13)⟩,
       ⟨((-4141 : Dyadic) * half ^ 13),
        ((-327 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((693 : Dyadic) * half ^ 11),
        ((-1647 : Dyadic) * half ^ 12)⟩,
       ⟨((-1713 : Dyadic) * half ^ 12),
        ((-847 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1223 : Dyadic) * half ^ 12),
        ((45 : Dyadic) * half ^ 13)⟩,
       ⟨((1217 : Dyadic) * half ^ 12),
        ((1257 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word13Step20 :
    word13Chunk20.foldl (fun acc a => a.applyPacked acc)
      word13State20 = word13State21 := by decide +kernel

private def word13Chunk21 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word13State22 : PackedMat2 :=
    ⟨⟨⟨((3333 : Dyadic) * half ^ 14),
        ((269 : Dyadic) * half ^ 11)⟩,
       ⟨((103 : Dyadic) * half ^ 14),
        ((-3167 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1481 : Dyadic) * half ^ 14),
        ((1145 : Dyadic) * half ^ 11)⟩,
       ⟨((5631 : Dyadic) * half ^ 14),
        ((-3625 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5631 : Dyadic) * half ^ 14),
        ((3625 : Dyadic) * half ^ 14)⟩,
       ⟨((-1481 : Dyadic) * half ^ 14),
        ((-1145 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((103 : Dyadic) * half ^ 14),
        ((-3167 : Dyadic) * half ^ 14)⟩,
       ⟨((3333 : Dyadic) * half ^ 14),
        ((269 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word13Step21 :
    word13Chunk21.foldl (fun acc a => a.applyPacked acc)
      word13State21 = word13State22 := by decide +kernel

private def word13Chunk22 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word13State23 : PackedMat2 :=
    ⟨⟨⟨((17739 : Dyadic) * half ^ 15),
        ((-8217 : Dyadic) * half ^ 15)⟩,
       ⟨((-12083 : Dyadic) * half ^ 15),
        ((-5841 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((413 : Dyadic) * half ^ 15),
        ((-2119 : Dyadic) * half ^ 15)⟩,
       ⟨((13987 : Dyadic) * half ^ 15),
        ((49 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2511 : Dyadic) * half ^ 15),
        ((6787 : Dyadic) * half ^ 15)⟩,
       ⟨((-1727 : Dyadic) * half ^ 15),
        ((225 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3465 : Dyadic) * half ^ 15),
        ((14911 : Dyadic) * half ^ 15)⟩,
       ⟨((19899 : Dyadic) * half ^ 15),
        ((-707 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word13Step22 :
    word13Chunk22.foldl (fun acc a => a.applyPacked acc)
      word13State22 = word13State23 := by decide +kernel

private def word13Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word13State24 : PackedMat2 :=
    ⟨⟨⟨((12689 : Dyadic) * half ^ 15),
        ((-18637 : Dyadic) * half ^ 16)⟩,
       ⟨((-815 : Dyadic) * half ^ 13),
        ((12135 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-14921 : Dyadic) * half ^ 15),
        ((-18173 : Dyadic) * half ^ 16)⟩,
       ⟨((4085 : Dyadic) * half ^ 13),
        ((299 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((14921 : Dyadic) * half ^ 15),
        ((18173 : Dyadic) * half ^ 16)⟩,
       ⟨((4085 : Dyadic) * half ^ 13),
        ((299 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((12689 : Dyadic) * half ^ 15),
        ((-18637 : Dyadic) * half ^ 16)⟩,
       ⟨((815 : Dyadic) * half ^ 13),
        ((-12135 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word13Step23 :
    word13Chunk23.foldl (fun acc a => a.applyPacked acc)
      word13State23 = word13State24 := by decide +kernel

private def word13Chunk24 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word13State25 : PackedMat2 :=
    ⟨⟨⟨((-57 : Dyadic) * half ^ 13),
        ((3927 : Dyadic) * half ^ 14)⟩,
       ⟨((10291 : Dyadic) * half ^ 14),
        ((-12429 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-341 : Dyadic) * half ^ 10),
        ((-24389 : Dyadic) * half ^ 16)⟩,
       ⟨((-5681 : Dyadic) * half ^ 15),
        ((593 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-25575 : Dyadic) * half ^ 16),
        ((-5231 : Dyadic) * half ^ 16)⟩,
       ⟨((23203 : Dyadic) * half ^ 16),
        ((16593 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-28137 : Dyadic) * half ^ 16),
        ((10405 : Dyadic) * half ^ 15)⟩,
       ⟨((3279 : Dyadic) * half ^ 16),
        ((10177 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word13Step24 :
    word13Chunk24.foldl (fun acc a => a.applyPacked acc)
      word13State24 = word13State25 := by decide +kernel

private def word13Chunk25 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word13State26 : PackedMat2 :=
    ⟨⟨⟨((2271 : Dyadic) * half ^ 16),
        ((-25219 : Dyadic) * half ^ 16)⟩,
       ⟨((44431 : Dyadic) * half ^ 16),
        ((7031 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4471 : Dyadic) * half ^ 16),
        ((-15115 : Dyadic) * half ^ 17)⟩,
       ⟨((14517 : Dyadic) * half ^ 15),
        ((-4571 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((4471 : Dyadic) * half ^ 16),
        ((15115 : Dyadic) * half ^ 17)⟩,
       ⟨((14517 : Dyadic) * half ^ 15),
        ((-4571 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2271 : Dyadic) * half ^ 16),
        ((-25219 : Dyadic) * half ^ 16)⟩,
       ⟨((-44431 : Dyadic) * half ^ 16),
        ((-7031 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word13Step25 :
    word13Chunk25.foldl (fun acc a => a.applyPacked acc)
      word13State25 = word13State26 := by decide +kernel

private def word13Chunk26 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word13State27 : PackedMat2 :=
    ⟨⟨⟨((-141931 : Dyadic) * half ^ 18),
        ((8181 : Dyadic) * half ^ 17)⟩,
       ⟨((-69659 : Dyadic) * half ^ 18),
        ((-19909 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-50557 : Dyadic) * half ^ 18),
        ((-29843 : Dyadic) * half ^ 17)⟩,
       ⟨((-180129 : Dyadic) * half ^ 18),
        ((11559 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-71245 : Dyadic) * half ^ 18),
        ((32393 : Dyadic) * half ^ 17)⟩,
       ⟨((48127 : Dyadic) * half ^ 18),
        ((115343 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-36271 : Dyadic) * half ^ 18),
        ((4517 : Dyadic) * half ^ 15)⟩,
       ⟨((-3547 : Dyadic) * half ^ 18),
        ((-105795 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word13Step26 :
    word13Chunk26.foldl (fun acc a => a.applyPacked acc)
      word13State26 = word13State27 := by decide +kernel

private def word13Chunk27 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word13State28 : PackedMat2 :=
    ⟨⟨⟨((-44515 : Dyadic) * half ^ 19),
        ((-63981 : Dyadic) * half ^ 19)⟩,
       ⟨((152735 : Dyadic) * half ^ 19),
        ((-631 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-178373 : Dyadic) * half ^ 19),
        ((183617 : Dyadic) * half ^ 19)⟩,
       ⟨((-298303 : Dyadic) * half ^ 19),
        ((-70801 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-325219 : Dyadic) * half ^ 19),
        ((-59965 : Dyadic) * half ^ 19)⟩,
       ⟨((42015 : Dyadic) * half ^ 19),
        ((-119169 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((16787 : Dyadic) * half ^ 19),
        ((-98625 : Dyadic) * half ^ 19)⟩,
       ⟨((144749 : Dyadic) * half ^ 19),
        ((-27055 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word13Step27 :
    word13Chunk27.foldl (fun acc a => a.applyPacked acc)
      word13State27 = word13State28 := by decide +kernel

private def word13Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word13State29 : PackedMat2 :=
    ⟨⟨⟨((-229535 : Dyadic) * half ^ 19),
        ((109935 : Dyadic) * half ^ 19)⟩,
       ⟨((23063 : Dyadic) * half ^ 18),
        ((57589 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((177513 : Dyadic) * half ^ 18),
        ((13605 : Dyadic) * half ^ 19)⟩,
       ⟨((-154421 : Dyadic) * half ^ 19),
        ((-97727 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((154421 : Dyadic) * half ^ 19),
        ((97727 : Dyadic) * half ^ 19)⟩,
       ⟨((-177513 : Dyadic) * half ^ 18),
        ((-13605 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((23063 : Dyadic) * half ^ 18),
        ((57589 : Dyadic) * half ^ 18)⟩,
       ⟨((-229535 : Dyadic) * half ^ 19),
        ((109935 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word13Step28 :
    word13Chunk28.foldl (fun acc a => a.applyPacked acc)
      word13State28 = word13State29 := by decide +kernel

private def word13Chunk29 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word13State30 : PackedMat2 :=
    ⟨⟨⟨((140325 : Dyadic) * half ^ 20),
        ((169079 : Dyadic) * half ^ 21)⟩,
       ⟨((358971 : Dyadic) * half ^ 20),
        ((-678605 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((281185 : Dyadic) * half ^ 19),
        ((631115 : Dyadic) * half ^ 21)⟩,
       ⟨((-153505 : Dyadic) * half ^ 19),
        ((439877 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-153505 : Dyadic) * half ^ 19),
        ((439877 : Dyadic) * half ^ 21)⟩,
       ⟨((281185 : Dyadic) * half ^ 19),
        ((631115 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-358971 : Dyadic) * half ^ 20),
        ((678605 : Dyadic) * half ^ 21)⟩,
       ⟨((-140325 : Dyadic) * half ^ 20),
        ((-169079 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word13Step29 :
    word13Chunk29.foldl (fun acc a => a.applyPacked acc)
      word13State29 = word13State30 := by decide +kernel

private def word13Chunk30 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word13State31 : PackedMat2 :=
    ⟨⟨⟨((-351389 : Dyadic) * half ^ 20),
        ((-304173 : Dyadic) * half ^ 20)⟩,
       ⟨((47523 : Dyadic) * half ^ 18),
        ((-663377 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-21891 : Dyadic) * half ^ 19),
        ((522065 : Dyadic) * half ^ 21)⟩,
       ⟨((-18315 : Dyadic) * half ^ 18),
        ((6911 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((362543 : Dyadic) * half ^ 21),
        ((-14739 : Dyadic) * half ^ 20)⟩,
       ⟨((1406673 : Dyadic) * half ^ 21),
        ((-58521 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((55031 : Dyadic) * half ^ 21),
        ((-541481 : Dyadic) * half ^ 21)⟩,
       ⟨((1271723 : Dyadic) * half ^ 21),
        ((161297 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word13Step30 :
    word13Chunk30.foldl (fun acc a => a.applyPacked acc)
      word13State30 = word13State31 := by decide +kernel

private def word13Chunk31 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word13State32 : PackedMat2 :=
    ⟨⟨⟨((722387 : Dyadic) * half ^ 21),
        ((-1240007 : Dyadic) * half ^ 22)⟩,
       ⟨((95819 : Dyadic) * half ^ 21),
        ((582629 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-395633 : Dyadic) * half ^ 20),
        ((2837 : Dyadic) * half ^ 21)⟩,
       ⟨((441023 : Dyadic) * half ^ 21),
        ((1788117 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-395633 : Dyadic) * half ^ 20),
        ((2837 : Dyadic) * half ^ 21)⟩,
       ⟨((-441023 : Dyadic) * half ^ 21),
        ((-1788117 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-722387 : Dyadic) * half ^ 21),
        ((1240007 : Dyadic) * half ^ 22)⟩,
       ⟨((95819 : Dyadic) * half ^ 21),
        ((582629 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word13Step31 :
    word13Chunk31.foldl (fun acc a => a.applyPacked acc)
      word13State31 = word13State32 := by decide +kernel

private def word13Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word13State33 : PackedMat2 :=
    ⟨⟨⟨((-4465443 : Dyadic) * half ^ 23),
        ((629759 : Dyadic) * half ^ 23)⟩,
       ⟨((5557733 : Dyadic) * half ^ 23),
        ((11495 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-945447 : Dyadic) * half ^ 23),
        ((-2552443 : Dyadic) * half ^ 23)⟩,
       ⟨((-411563 : Dyadic) * half ^ 23),
        ((94643 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((4066731 : Dyadic) * half ^ 23),
        ((133471 : Dyadic) * half ^ 22)⟩,
       ⟨((-1038155 : Dyadic) * half ^ 23),
        ((-678505 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((445839 : Dyadic) * half ^ 23),
        ((-1252897 : Dyadic) * half ^ 21)⟩,
       ⟨((-813679 : Dyadic) * half ^ 23),
        ((-546145 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word13Step32 :
    word13Chunk32.foldl (fun acc a => a.applyPacked acc)
      word13State32 = word13State33 := by decide +kernel

private def word13Chunk33 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word13State34 : PackedMat2 :=
    ⟨⟨⟨((-52387 : Dyadic) * half ^ 18),
        ((-262115 : Dyadic) * half ^ 21)⟩,
       ⟨((-2254583 : Dyadic) * half ^ 23),
        ((1925445 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-4579383 : Dyadic) * half ^ 23),
        ((-228747 : Dyadic) * half ^ 21)⟩,
       ⟨((-868651 : Dyadic) * half ^ 22),
        ((-1573963 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((868651 : Dyadic) * half ^ 22),
        ((1573963 : Dyadic) * half ^ 23)⟩,
       ⟨((4579383 : Dyadic) * half ^ 23),
        ((228747 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-2254583 : Dyadic) * half ^ 23),
        ((1925445 : Dyadic) * half ^ 22)⟩,
       ⟨((-52387 : Dyadic) * half ^ 18),
        ((-262115 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word13Step33 :
    word13Chunk33.foldl (fun acc a => a.applyPacked acc)
      word13State33 = word13State34 := by decide +kernel

private def word13Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word13State35 : PackedMat2 :=
    ⟨⟨⟨((-599377 : Dyadic) * half ^ 23),
        ((-15559643 : Dyadic) * half ^ 25)⟩,
       ⟨((2705685 : Dyadic) * half ^ 24),
        ((8174587 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-456831 : Dyadic) * half ^ 21),
        ((-2901815 : Dyadic) * half ^ 25)⟩,
       ⟨((-9230243 : Dyadic) * half ^ 24),
        ((5565959 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-456831 : Dyadic) * half ^ 21),
        ((-2901815 : Dyadic) * half ^ 25)⟩,
       ⟨((9230243 : Dyadic) * half ^ 24),
        ((-5565959 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((599377 : Dyadic) * half ^ 23),
        ((15559643 : Dyadic) * half ^ 25)⟩,
       ⟨((2705685 : Dyadic) * half ^ 24),
        ((8174587 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word13Step34 :
    word13Chunk34.foldl (fun acc a => a.applyPacked acc)
      word13State34 = word13State35 := by decide +kernel

private def word13Chunk35 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word13State36 : PackedMat2 :=
    ⟨⟨⟨((-13864053 : Dyadic) * half ^ 25),
        ((-18191187 : Dyadic) * half ^ 26)⟩,
       ⟨((-732583 : Dyadic) * half ^ 22),
        ((20073463 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3727271 : Dyadic) * half ^ 25),
        ((29203779 : Dyadic) * half ^ 26)⟩,
       ⟨((967063 : Dyadic) * half ^ 24),
        ((-13292495 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3977821 : Dyadic) * half ^ 24),
        ((1793145 : Dyadic) * half ^ 26)⟩,
       ⟨((-21248137 : Dyadic) * half ^ 25),
        ((5661397 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((470569 : Dyadic) * half ^ 24),
        ((-19724717 : Dyadic) * half ^ 26)⟩,
       ⟨((-19132325 : Dyadic) * half ^ 25),
        ((-8003389 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word13Step35 :
    word13Chunk35.foldl (fun acc a => a.applyPacked acc)
      word13State35 = word13State36 := by decide +kernel

private def word13Chunk36 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word13State37 : PackedMat2 :=
    ⟨⟨⟨((-14264649 : Dyadic) * half ^ 26),
        ((-17254537 : Dyadic) * half ^ 26)⟩,
       ⟨((9936681 : Dyadic) * half ^ 26),
        ((-29558147 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((21408989 : Dyadic) * half ^ 26),
        ((3238927 : Dyadic) * half ^ 24)⟩,
       ⟨((-30883819 : Dyadic) * half ^ 26),
        ((3720211 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2757643 : Dyadic) * half ^ 25),
        ((6536601 : Dyadic) * half ^ 24)⟩,
       ⟨((-10198065 : Dyadic) * half ^ 25),
        ((4737415 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-6151805 : Dyadic) * half ^ 25),
        ((12100665 : Dyadic) * half ^ 26)⟩,
       ⟨((-11703171 : Dyadic) * half ^ 24),
        ((-135249 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word13Step36 :
    word13Chunk36.foldl (fun acc a => a.applyPacked acc)
      word13State36 = word13State37 := by decide +kernel

private def word13Chunk37 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word13State38 : PackedMat2 :=
    ⟨⟨⟨((-49961041 : Dyadic) * half ^ 27),
        ((-5426453 : Dyadic) * half ^ 26)⟩,
       ⟨((-52984813 : Dyadic) * half ^ 27),
        ((-12055271 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((69098845 : Dyadic) * half ^ 27),
        ((933951 : Dyadic) * half ^ 26)⟩,
       ⟨((83102517 : Dyadic) * half ^ 27),
        ((-15764127 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((83102517 : Dyadic) * half ^ 27),
        ((-15764127 : Dyadic) * half ^ 27)⟩,
       ⟨((69098845 : Dyadic) * half ^ 27),
        ((933951 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((52984813 : Dyadic) * half ^ 27),
        ((12055271 : Dyadic) * half ^ 27)⟩,
       ⟨((49961041 : Dyadic) * half ^ 27),
        ((5426453 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word13Step37 :
    word13Chunk37.foldl (fun acc a => a.applyPacked acc)
      word13State37 = word13State38 := by decide +kernel

private def word13Chunk38 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word13State39 : PackedMat2 :=
    ⟨⟨⟨((22121263 : Dyadic) * half ^ 28),
        ((25576675 : Dyadic) * half ^ 27)⟩,
       ⟨((-40406903 : Dyadic) * half ^ 28),
        ((-33689193 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((173025035 : Dyadic) * half ^ 28),
        ((-2194339 : Dyadic) * half ^ 25)⟩,
       ⟨((4314533 : Dyadic) * half ^ 28),
        ((126213427 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-4314533 : Dyadic) * half ^ 28),
        ((-126213427 : Dyadic) * half ^ 28)⟩,
       ⟨((-173025035 : Dyadic) * half ^ 28),
        ((2194339 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-40406903 : Dyadic) * half ^ 28),
        ((-33689193 : Dyadic) * half ^ 28)⟩,
       ⟨((22121263 : Dyadic) * half ^ 28),
        ((25576675 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word13Step38 :
    word13Chunk38.foldl (fun acc a => a.applyPacked acc)
      word13State38 = word13State39 := by decide +kernel

private def word13Chunk39 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word13State40 : PackedMat2 :=
    ⟨⟨⟨((87032379 : Dyadic) * half ^ 29),
        ((-82649449 : Dyadic) * half ^ 29)⟩,
       ⟨((-368018979 : Dyadic) * half ^ 29),
        ((-8786569 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-160367979 : Dyadic) * half ^ 29),
        ((-34999005 : Dyadic) * half ^ 29)⟩,
       ⟨((-122620713 : Dyadic) * half ^ 29),
        ((49519641 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((233077569 : Dyadic) * half ^ 29),
        ((18873633 : Dyadic) * half ^ 29)⟩,
       ⟨((163079559 : Dyadic) * half ^ 29),
        ((-70747173 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-12356897 : Dyadic) * half ^ 29),
        ((227525679 : Dyadic) * half ^ 29)⟩,
       ⟨((152942001 : Dyadic) * half ^ 29),
        ((35123325 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word13Step39 :
    word13Chunk39.foldl (fun acc a => a.applyPacked acc)
      word13State39 = word13State40 := by decide +kernel

private def word13Chunk40 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word13State41 : PackedMat2 :=
    ⟨⟨⟨((17257947 : Dyadic) * half ^ 28),
        ((-85861915 : Dyadic) * half ^ 29)⟩,
       ⟨((-215854631 : Dyadic) * half ^ 29),
        ((-119486667 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((68844595 : Dyadic) * half ^ 29),
        ((-301048797 : Dyadic) * half ^ 29)⟩,
       ⟨((-50713281 : Dyadic) * half ^ 28),
        ((10364973 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((280318851 : Dyadic) * half ^ 29),
        ((32581967 : Dyadic) * half ^ 30)⟩,
       ⟨((321778743 : Dyadic) * half ^ 29),
        ((-170271157 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-102674291 : Dyadic) * half ^ 28),
        ((-181338737 : Dyadic) * half ^ 30)⟩,
       ⟨((2101547 : Dyadic) * half ^ 25),
        ((250370525 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word13Step40 :
    word13Chunk40.foldl (fun acc a => a.applyPacked acc)
      word13State40 = word13State41 := by decide +kernel

private def word13Chunk41 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word13State42 : PackedMat2 :=
    ⟨⟨⟨((73059447 : Dyadic) * half ^ 29),
        ((1263165283 : Dyadic) * half ^ 31)⟩,
       ⟨((-56404619 : Dyadic) * half ^ 30),
        ((-72629341 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-127340441 : Dyadic) * half ^ 29),
        ((559185029 : Dyadic) * half ^ 31)⟩,
       ⟨((105806937 : Dyadic) * half ^ 30),
        ((-437166119 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-127340441 : Dyadic) * half ^ 29),
        ((559185029 : Dyadic) * half ^ 31)⟩,
       ⟨((-105806937 : Dyadic) * half ^ 30),
        ((437166119 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-73059447 : Dyadic) * half ^ 29),
        ((-1263165283 : Dyadic) * half ^ 31)⟩,
       ⟨((-56404619 : Dyadic) * half ^ 30),
        ((-72629341 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word13Step41 :
    word13Chunk41.foldl (fun acc a => a.applyPacked acc)
      word13State41 = word13State42 := by decide +kernel

private def word13Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word13State43 : PackedMat2 :=
    ⟨⟨⟨((-233264553 : Dyadic) * half ^ 30),
        ((1377674011 : Dyadic) * half ^ 32)⟩,
       ⟨((523862553 : Dyadic) * half ^ 31),
        ((158882393 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-5257637 : Dyadic) * half ^ 30),
        ((-1846826117 : Dyadic) * half ^ 32)⟩,
       ⟨((-329412593 : Dyadic) * half ^ 31),
        ((-1639502003 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((435791015 : Dyadic) * half ^ 29),
        ((339927867 : Dyadic) * half ^ 32)⟩,
       ⟨((103662057 : Dyadic) * half ^ 31),
        ((-318897319 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((384139101 : Dyadic) * half ^ 30),
        ((57333447 : Dyadic) * half ^ 32)⟩,
       ⟨((609395809 : Dyadic) * half ^ 31),
        ((-990391659 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word13Step42 :
    word13Chunk42.foldl (fun acc a => a.applyPacked acc)
      word13State42 = word13State43 := by decide +kernel

private def word13Chunk43 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word13State44 : PackedMat2 :=
    ⟨⟨⟨((524398865 : Dyadic) * half ^ 32),
        ((-170715163 : Dyadic) * half ^ 29)⟩,
       ⟨((-318161987 : Dyadic) * half ^ 32),
        ((72321625 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-2041276077 : Dyadic) * half ^ 32),
        ((729794531 : Dyadic) * half ^ 32)⟩,
       ⟨((-1183488171 : Dyadic) * half ^ 32),
        ((-1941662657 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2041276077 : Dyadic) * half ^ 32),
        ((729794531 : Dyadic) * half ^ 32)⟩,
       ⟨((1183488171 : Dyadic) * half ^ 32),
        ((1941662657 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-524398865 : Dyadic) * half ^ 32),
        ((170715163 : Dyadic) * half ^ 29)⟩,
       ⟨((-318161987 : Dyadic) * half ^ 32),
        ((72321625 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word13Step43 :
    word13Chunk43.foldl (fun acc a => a.applyPacked acc)
      word13State43 = word13State44 := by decide +kernel

private def word13Chunk44 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word13State45 : PackedMat2 :=
    ⟨⟨⟨((-3625148747 : Dyadic) * half ^ 33),
        ((-1377269759 : Dyadic) * half ^ 33)⟩,
       ⟨((3774429053 : Dyadic) * half ^ 33),
        ((-528194311 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((3719512037 : Dyadic) * half ^ 33),
        ((-202731859 : Dyadic) * half ^ 33)⟩,
       ⟨((-4269593587 : Dyadic) * half ^ 33),
        ((-437487033 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-672242207 : Dyadic) * half ^ 33),
        ((-998638203 : Dyadic) * half ^ 31)⟩,
       ⟨((-1077705925 : Dyadic) * half ^ 33),
        ((-275040775 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((735507485 : Dyadic) * half ^ 33),
        ((-924947225 : Dyadic) * half ^ 31)⟩,
       ⟨((3490047003 : Dyadic) * half ^ 33),
        ((-74640153 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word13Step44 :
    word13Chunk44.foldl (fun acc a => a.applyPacked acc)
      word13State44 = word13State45 := by decide +kernel

private def word13Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word13State46 : PackedMat2 :=
    ⟨⟨⟨((-868896071 : Dyadic) * half ^ 34),
        ((-4763952025 : Dyadic) * half ^ 33)⟩,
       ⟨((-2317542703 : Dyadic) * half ^ 34),
        ((-4779337719 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3804883161 : Dyadic) * half ^ 34),
        ((1036419003 : Dyadic) * half ^ 32)⟩,
       ⟨((-3236853505 : Dyadic) * half ^ 34),
        ((1106403115 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3039272897 : Dyadic) * half ^ 34),
        ((-71003707 : Dyadic) * half ^ 32)⟩,
       ⟨((-5252079127 : Dyadic) * half ^ 34),
        ((3520868333 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((4748566331 : Dyadic) * half ^ 34),
        ((-181080829 : Dyadic) * half ^ 32)⟩,
       ⟨((-14307241769 : Dyadic) * half ^ 34),
        ((-1593219387 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word13Step45 :
    word13Chunk45.foldl (fun acc a => a.applyPacked acc)
      word13State45 = word13State46 := by decide +kernel

private def word13Chunk46 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word13State47 : PackedMat2 :=
    ⟨⟨⟨((-3233345559 : Dyadic) * half ^ 33),
        ((-58808591 : Dyadic) * half ^ 33)⟩,
       ⟨((-6832212507 : Dyadic) * half ^ 34),
        ((-5369521819 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5329654729 : Dyadic) * half ^ 34),
        ((-7219595163 : Dyadic) * half ^ 34)⟩,
       ⟨((181366443 : Dyadic) * half ^ 33),
        ((2844080113 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2187757525 : Dyadic) * half ^ 33),
        ((5692387615 : Dyadic) * half ^ 35)⟩,
       ⟨((-2515918819 : Dyadic) * half ^ 32),
        ((4966921843 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((5487139001 : Dyadic) * half ^ 34),
        ((13298903625 : Dyadic) * half ^ 35)⟩,
       ⟨((-5251904637 : Dyadic) * half ^ 34),
        ((-365521389 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word13Step46 :
    word13Chunk46.foldl (fun acc a => a.applyPacked acc)
      word13State46 = word13State47 := by decide +kernel

private def word13Chunk47 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word13State48 : PackedMat2 :=
    ⟨⟨⟨((-10617464689 : Dyadic) * half ^ 35),
        ((27242212785 : Dyadic) * half ^ 36)⟩,
       ⟨((-13597167807 : Dyadic) * half ^ 35),
        ((-27431121693 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2634706707 : Dyadic) * half ^ 34),
        ((-13147002733 : Dyadic) * half ^ 36)⟩,
       ⟨((-682684619 : Dyadic) * half ^ 33),
        ((5297226399 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((682684619 : Dyadic) * half ^ 33),
        ((-5297226399 : Dyadic) * half ^ 36)⟩,
       ⟨((-2634706707 : Dyadic) * half ^ 34),
        ((13147002733 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-13597167807 : Dyadic) * half ^ 35),
        ((-27431121693 : Dyadic) * half ^ 36)⟩,
       ⟨((-10617464689 : Dyadic) * half ^ 35),
        ((27242212785 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word13Step47 :
    word13Chunk47.foldl (fun acc a => a.applyPacked acc)
      word13State47 = word13State48 := by decide +kernel

private def word13Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word13State49 : PackedMat2 :=
    ⟨⟨⟨((54282038211 : Dyadic) * half ^ 36),
        ((-2128614373 : Dyadic) * half ^ 37)⟩,
       ⟨((-1192082375 : Dyadic) * half ^ 35),
        ((43605704715 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-25357957311 : Dyadic) * half ^ 36),
        ((-11581193469 : Dyadic) * half ^ 37)⟩,
       ⟨((-3271100483 : Dyadic) * half ^ 35),
        ((11336658591 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-122267439 : Dyadic) * half ^ 36),
        ((-31900158277 : Dyadic) * half ^ 37)⟩,
       ⟨((-5729463015 : Dyadic) * half ^ 35),
        ((-18815756345 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-20738545171 : Dyadic) * half ^ 36),
        ((-51897873461 : Dyadic) * half ^ 37)⟩,
       ⟨((2858394943 : Dyadic) * half ^ 33),
        ((-56666202961 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word13Step48 :
    word13Chunk48.foldl (fun acc a => a.applyPacked acc)
      word13State48 = word13State49 := by decide +kernel

private def word13Chunk49 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word13State50 : PackedMat2 :=
    ⟨⟨⟨((-6286650589 : Dyadic) * half ^ 37),
        ((38147515149 : Dyadic) * half ^ 37)⟩,
       ⟨((72529785615 : Dyadic) * half ^ 37),
        ((-9239068671 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-2654827753 : Dyadic) * half ^ 37),
        ((-13207284741 : Dyadic) * half ^ 35)⟩,
       ⟨((-68303336931 : Dyadic) * half ^ 37),
        ((-5634245257 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2654827753 : Dyadic) * half ^ 37),
        ((13207284741 : Dyadic) * half ^ 35)⟩,
       ⟨((-68303336931 : Dyadic) * half ^ 37),
        ((-5634245257 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-6286650589 : Dyadic) * half ^ 37),
        ((38147515149 : Dyadic) * half ^ 37)⟩,
       ⟨((-72529785615 : Dyadic) * half ^ 37),
        ((9239068671 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word13Step49 :
    word13Chunk49.foldl (fun acc a => a.applyPacked acc)
      word13State49 = word13State50 := by decide +kernel

private def word13Chunk50 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word13State51 : PackedMat2 :=
    ⟨⟨⟨((-60332384795 : Dyadic) * half ^ 38),
        ((-8131666065 : Dyadic) * half ^ 36)⟩,
       ⟨((-66325436381 : Dyadic) * half ^ 38),
        ((143501555353 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-66263387475 : Dyadic) * half ^ 38),
        ((-1531744047 : Dyadic) * half ^ 34)⟩,
       ⟨((-72578392601 : Dyadic) * half ^ 38),
        ((-81724257793 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((72578392601 : Dyadic) * half ^ 38),
        ((81724257793 : Dyadic) * half ^ 38)⟩,
       ⟨((66263387475 : Dyadic) * half ^ 38),
        ((1531744047 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-66325436381 : Dyadic) * half ^ 38),
        ((143501555353 : Dyadic) * half ^ 38)⟩,
       ⟨((-60332384795 : Dyadic) * half ^ 38),
        ((-8131666065 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word13Step50 :
    word13Chunk50.foldl (fun acc a => a.applyPacked acc)
      word13State50 = word13State51 := by decide +kernel

private def word13Chunk51 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word13State52 : PackedMat2 :=
    ⟨⟨⟨((-155924429069 : Dyadic) * half ^ 39),
        ((-67393668341 : Dyadic) * half ^ 39)⟩,
       ⟨((-83614255999 : Dyadic) * half ^ 39),
        ((88251914141 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-12183873447 : Dyadic) * half ^ 39),
        ((126043106013 : Dyadic) * half ^ 39)⟩,
       ⟨((-20009106245 : Dyadic) * half ^ 39),
        ((-2258975475 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-415191966813 : Dyadic) * half ^ 39),
        ((-3912616399 : Dyadic) * half ^ 39)⟩,
       ⟨((-163105754787 : Dyadic) * half ^ 39),
        ((-8048244923 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-243897496623 : Dyadic) * half ^ 39),
        ((-36155086535 : Dyadic) * half ^ 39)⟩,
       ⟨((-109110159941 : Dyadic) * half ^ 39),
        ((59884671267 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word13Step51 :
    word13Chunk51.foldl (fun acc a => a.applyPacked acc)
      word13State51 = word13State52 := by decide +kernel

private def word13Chunk52 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word13State53 : PackedMat2 :=
    ⟨⟨⟨((-9747301809 : Dyadic) * half ^ 38),
        ((-114617840841 : Dyadic) * half ^ 38)⟩,
       ⟨((88537060625 : Dyadic) * half ^ 39),
        ((-110039196285 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((58085444601 : Dyadic) * half ^ 39),
        ((52392829753 : Dyadic) * half ^ 38)⟩,
       ⟨((-63358417381 : Dyadic) * half ^ 37),
        ((-35234914257 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-69550745249 : Dyadic) * half ^ 39),
        ((195348224923 : Dyadic) * half ^ 40)⟩,
       ⟨((-140020573763 : Dyadic) * half ^ 39),
        ((-311519114125 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-112328518563 : Dyadic) * half ^ 37),
        ((69042457007 : Dyadic) * half ^ 40)⟩,
       ⟨((-1144661139 : Dyadic) * half ^ 36),
        ((-108031664243 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word13Step52 :
    word13Chunk52.foldl (fun acc a => a.applyPacked acc)
      word13State52 = word13State53 := by decide +kernel

private def word13Chunk53 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word13State54 : PackedMat2 :=
    ⟨⟨⟨((-2129456105 : Dyadic) * half ^ 34),
        ((581025165249 : Dyadic) * half ^ 41)⟩,
       ⟨((-810779408019 : Dyadic) * half ^ 40),
        ((-19741949731 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((78968548767 : Dyadic) * half ^ 38),
        ((-286053739737 : Dyadic) * half ^ 41)⟩,
       ⟨((292532798749 : Dyadic) * half ^ 40),
        ((524849707743 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((119397984003 : Dyadic) * half ^ 40),
        ((608406993817 : Dyadic) * half ^ 41)⟩,
       ⟨((-101362930935 : Dyadic) * half ^ 38),
        ((23341396319 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-280641607759 : Dyadic) * half ^ 40),
        ((947064598739 : Dyadic) * half ^ 41)⟩,
       ⟨((-150191778745 : Dyadic) * half ^ 39),
        ((-674494217299 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word13Step53 :
    word13Chunk53.foldl (fun acc a => a.applyPacked acc)
      word13State53 = word13State54 := by decide +kernel

private def word13Chunk54 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word13State55 : PackedMat2 :=
    ⟨⟨⟨((1684337372017 : Dyadic) * half ^ 41),
        ((136010638017 : Dyadic) * half ^ 41)⟩,
       ⟨((159847054617 : Dyadic) * half ^ 41),
        ((-663293695263 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((232192869533 : Dyadic) * half ^ 41),
        ((31660158031 : Dyadic) * half ^ 40)⟩,
       ⟨((977009093531 : Dyadic) * half ^ 41),
        ((-8812915859 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-102163484903 : Dyadic) * half ^ 40),
        ((372408111999 : Dyadic) * half ^ 41)⟩,
       ⟨((-38843168841 : Dyadic) * half ^ 40),
        ((151150245383 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((24978260415 : Dyadic) * half ^ 36),
        ((190561289675 : Dyadic) * half ^ 39)⟩,
       ⟨((263641528623 : Dyadic) * half ^ 40),
        ((-922092213317 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word13Step54 :
    word13Chunk54.foldl (fun acc a => a.applyPacked acc)
      word13State54 = word13State55 := by decide +kernel

private def word13Chunk55 : List Letter := [.h, .t, .h]
private def word13State56 : PackedMat2 :=
    ⟨⟨⟨((78484612657 : Dyadic) * half ^ 37),
        ((666992112389 : Dyadic) * half ^ 41)⟩,
       ⟨((-711065716921 : Dyadic) * half ^ 41),
        ((502203076665 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-224256599699 : Dyadic) * half ^ 41),
        ((158573362373 : Dyadic) * half ^ 41)⟩,
       ⟨((12394163029 : Dyadic) * half ^ 35),
        ((-140223947599 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((224256599699 : Dyadic) * half ^ 41),
        ((-158573362373 : Dyadic) * half ^ 41)⟩,
       ⟨((12394163029 : Dyadic) * half ^ 35),
        ((-140223947599 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((78484612657 : Dyadic) * half ^ 37),
        ((666992112389 : Dyadic) * half ^ 41)⟩,
       ⟨((711065716921 : Dyadic) * half ^ 41),
        ((-502203076665 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word13Step55 :
    word13Chunk55.foldl (fun acc a => a.applyPacked acc)
      word13State55 = word13State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word13_check : check word13 13 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word13 = word13State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word13Chunk0 ++ word13Chunk1 ++ word13Chunk2 ++ word13Chunk3 ++
      word13Chunk4 ++ word13Chunk5 ++ word13Chunk6 ++ word13Chunk7 ++
      word13Chunk8 ++ word13Chunk9 ++ word13Chunk10 ++ word13Chunk11 ++
      word13Chunk12 ++ word13Chunk13 ++ word13Chunk14 ++ word13Chunk15 ++
      word13Chunk16 ++ word13Chunk17 ++ word13Chunk18 ++ word13Chunk19 ++
      word13Chunk20 ++ word13Chunk21 ++ word13Chunk22 ++ word13Chunk23 ++
      word13Chunk24 ++ word13Chunk25 ++ word13Chunk26 ++ word13Chunk27 ++
      word13Chunk28 ++ word13Chunk29 ++ word13Chunk30 ++ word13Chunk31 ++
      word13Chunk32 ++ word13Chunk33 ++ word13Chunk34 ++ word13Chunk35 ++
      word13Chunk36 ++ word13Chunk37 ++ word13Chunk38 ++ word13Chunk39 ++
      word13Chunk40 ++ word13Chunk41 ++ word13Chunk42 ++ word13Chunk43 ++
      word13Chunk44 ++ word13Chunk45 ++ word13Chunk46 ++ word13Chunk47 ++
      word13Chunk48 ++ word13Chunk49 ++ word13Chunk50 ++ word13Chunk51 ++
      word13Chunk52 ++ word13Chunk53 ++ word13Chunk54 ++ word13Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word13Step0, word13Step1, word13Step2, word13Step3, word13Step4,
      word13Step5, word13Step6, word13Step7, word13Step8, word13Step9,
      word13Step10, word13Step11, word13Step12, word13Step13, word13Step14,
      word13Step15, word13Step16, word13Step17, word13Step18, word13Step19,
      word13Step20, word13Step21, word13Step22, word13Step23, word13Step24,
      word13Step25, word13Step26, word13Step27, word13Step28, word13Step29,
      word13Step30, word13Step31, word13Step32, word13Step33, word13Step34,
      word13Step35, word13Step36, word13Step37, word13Step38, word13Step39,
      word13Step40, word13Step41, word13Step42, word13Step43, word13Step44,
      word13Step45, word13Step46, word13Step47, word13Step48, word13Step49,
      word13Step50, word13Step51, word13Step52, word13Step53, word13Step54,
      word13Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
