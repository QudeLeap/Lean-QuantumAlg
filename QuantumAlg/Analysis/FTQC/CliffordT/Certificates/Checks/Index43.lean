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
private def word43Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word43State1 : PackedMat2 :=
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
private lemma word43Step0 :
    word43Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word43State1 := by decide +kernel

private def word43Chunk1 : List Letter := [.h, .s, .h, .s, .s, .h, .s, .t]
private def word43State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word43Step1 :
    word43Chunk1.foldl (fun acc a => a.applyPacked acc)
      word43State1 = word43State2 := by decide +kernel

private def word43Chunk2 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word43State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word43Step2 :
    word43Chunk2.foldl (fun acc a => a.applyPacked acc)
      word43State2 = word43State3 := by decide +kernel

private def word43Chunk3 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word43State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-7 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word43Step3 :
    word43Chunk3.foldl (fun acc a => a.applyPacked acc)
      word43State3 = word43State4 := by decide +kernel

private def word43Chunk4 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word43State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word43Step4 :
    word43Chunk4.foldl (fun acc a => a.applyPacked acc)
      word43State4 = word43State5 := by decide +kernel

private def word43Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word43State6 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((9 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word43Step5 :
    word43Chunk5.foldl (fun acc a => a.applyPacked acc)
      word43State5 = word43State6 := by decide +kernel

private def word43Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word43State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word43Step6 :
    word43Chunk6.foldl (fun acc a => a.applyPacked acc)
      word43State6 = word43State7 := by decide +kernel

private def word43Chunk7 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word43State8 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((53 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 6),
        (0 : Dyadic)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word43Step7 :
    word43Chunk7.foldl (fun acc a => a.applyPacked acc)
      word43State7 = word43State8 := by decide +kernel

private def word43Chunk8 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word43State9 : PackedMat2 :=
    ⟨⟨⟨((-31 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((51 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((21 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((51 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word43Step8 :
    word43Chunk8.foldl (fun acc a => a.applyPacked acc)
      word43State8 = word43State9 := by decide +kernel

private def word43Chunk9 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word43State10 : PackedMat2 :=
    ⟨⟨⟨((37 : Dyadic) * half ^ 7),
        ((-85 : Dyadic) * half ^ 8)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((53 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 6),
        ((-35 : Dyadic) * half ^ 8)⟩,
       ⟨((-51 : Dyadic) * half ^ 7),
        ((-71 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-51 : Dyadic) * half ^ 7),
        ((-71 : Dyadic) * half ^ 8)⟩,
       ⟨((-25 : Dyadic) * half ^ 6),
        ((-35 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((-53 : Dyadic) * half ^ 8)⟩,
       ⟨((-37 : Dyadic) * half ^ 7),
        ((85 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word43Step9 :
    word43Chunk9.foldl (fun acc a => a.applyPacked acc)
      word43State9 = word43State10 := by decide +kernel

private def word43Chunk10 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word43State11 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 7)⟩,
       ⟨((35 : Dyadic) * half ^ 6),
        ((-67 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((-111 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((99 : Dyadic) * half ^ 8),
        ((55 : Dyadic) * half ^ 8)⟩,
       ⟨((-123 : Dyadic) * half ^ 8),
        ((-29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 8),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((113 : Dyadic) * half ^ 8),
        ((-33 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word43Step10 :
    word43Chunk10.foldl (fun acc a => a.applyPacked acc)
      word43State10 = word43State11 := by decide +kernel

private def word43Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word43State12 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 9),
        ((-57 : Dyadic) * half ^ 9)⟩,
       ⟨((-237 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((241 : Dyadic) * half ^ 9),
        ((87 : Dyadic) * half ^ 8)⟩,
       ⟨((-181 : Dyadic) * half ^ 9),
        ((135 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((241 : Dyadic) * half ^ 9),
        ((87 : Dyadic) * half ^ 8)⟩,
       ⟨((181 : Dyadic) * half ^ 9),
        ((-135 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 9),
        ((57 : Dyadic) * half ^ 9)⟩,
       ⟨((-237 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word43Step11 :
    word43Chunk11.foldl (fun acc a => a.applyPacked acc)
      word43State11 = word43State12 := by decide +kernel

private def word43Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word43State13 : PackedMat2 :=
    ⟨⟨⟨((91 : Dyadic) * half ^ 8),
        ((89 : Dyadic) * half ^ 10)⟩,
       ⟨((81 : Dyadic) * half ^ 8),
        ((-429 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((269 : Dyadic) * half ^ 9),
        ((163 : Dyadic) * half ^ 10)⟩,
       ⟨((137 : Dyadic) * half ^ 9),
        ((69 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-47 : Dyadic) * half ^ 9),
        ((-33 : Dyadic) * half ^ 8)⟩,
       ⟨((29 : Dyadic) * half ^ 7),
        ((203 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((259 : Dyadic) * half ^ 9),
        ((5 : Dyadic) * half ^ 8)⟩,
       ⟨((85 : Dyadic) * half ^ 8),
        ((-43 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word43Step12 :
    word43Chunk12.foldl (fun acc a => a.applyPacked acc)
      word43State12 = word43State13 := by decide +kernel

private def word43Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word43State14 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 8),
        ((429 : Dyadic) * half ^ 11)⟩,
       ⟨((119 : Dyadic) * half ^ 10),
        ((1025 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-521 : Dyadic) * half ^ 10),
        ((329 : Dyadic) * half ^ 11)⟩,
       ⟨((33 : Dyadic) * half ^ 9),
        ((411 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 9),
        ((-411 : Dyadic) * half ^ 11)⟩,
       ⟨((521 : Dyadic) * half ^ 10),
        ((-329 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((119 : Dyadic) * half ^ 10),
        ((1025 : Dyadic) * half ^ 11)⟩,
       ⟨((13 : Dyadic) * half ^ 8),
        ((429 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word43Step13 :
    word43Chunk13.foldl (fun acc a => a.applyPacked acc)
      word43State13 = word43State14 := by decide +kernel

private def word43Chunk14 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word43State15 : PackedMat2 :=
    ⟨⟨⟨((-703 : Dyadic) * half ^ 11),
        ((105 : Dyadic) * half ^ 12)⟩,
       ⟨((69 : Dyadic) * half ^ 7),
        ((1083 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 9),
        ((563 : Dyadic) * half ^ 12)⟩,
       ⟨((1009 : Dyadic) * half ^ 11),
        ((-1181 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1009 : Dyadic) * half ^ 11),
        ((-1181 : Dyadic) * half ^ 12)⟩,
       ⟨((31 : Dyadic) * half ^ 9),
        ((563 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 7),
        ((-1083 : Dyadic) * half ^ 12)⟩,
       ⟨((703 : Dyadic) * half ^ 11),
        ((-105 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word43Step14 :
    word43Chunk14.foldl (fun acc a => a.applyPacked acc)
      word43State14 = word43State15 := by decide +kernel

private def word43Chunk15 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word43State16 : PackedMat2 :=
    ⟨⟨⟨((-251 : Dyadic) * half ^ 9),
        ((-327 : Dyadic) * half ^ 11)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((875 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((329 : Dyadic) * half ^ 11),
        ((157 : Dyadic) * half ^ 9)⟩,
       ⟨((-55 : Dyadic) * half ^ 7),
        ((1343 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-2599 : Dyadic) * half ^ 12),
        ((551 : Dyadic) * half ^ 12)⟩,
       ⟨((87 : Dyadic) * half ^ 12),
        ((-1209 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((221 : Dyadic) * half ^ 12),
        ((-219 : Dyadic) * half ^ 10)⟩,
       ⟨((-1529 : Dyadic) * half ^ 12),
        ((-283 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word43Step15 :
    word43Chunk15.foldl (fun acc a => a.applyPacked acc)
      word43State15 = word43State16 := by decide +kernel

private def word43Chunk16 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word43State17 : PackedMat2 :=
    ⟨⟨⟨((-87 : Dyadic) * half ^ 10),
        ((-2989 : Dyadic) * half ^ 13)⟩,
       ⟨((-23 : Dyadic) * half ^ 12),
        ((-583 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-99 : Dyadic) * half ^ 8),
        ((2161 : Dyadic) * half ^ 13)⟩,
       ⟨((-31 : Dyadic) * half ^ 6),
        ((-587 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 6),
        ((-587 : Dyadic) * half ^ 12)⟩,
       ⟨((-99 : Dyadic) * half ^ 8),
        ((2161 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 12),
        ((583 : Dyadic) * half ^ 11)⟩,
       ⟨((87 : Dyadic) * half ^ 10),
        ((2989 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word43Step16 :
    word43Chunk16.foldl (fun acc a => a.applyPacked acc)
      word43State16 = word43State17 := by decide +kernel

private def word43Chunk17 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word43State18 : PackedMat2 :=
    ⟨⟨⟨((-6919 : Dyadic) * half ^ 14),
        ((1301 : Dyadic) * half ^ 12)⟩,
       ⟨((-8695 : Dyadic) * half ^ 14),
        ((-3435 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2969 : Dyadic) * half ^ 14),
        ((-2365 : Dyadic) * half ^ 14)⟩,
       ⟨((-6173 : Dyadic) * half ^ 14),
        ((-533 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((4497 : Dyadic) * half ^ 14),
        ((801 : Dyadic) * half ^ 13)⟩,
       ⟨((233 : Dyadic) * half ^ 14),
        ((-4571 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1769 : Dyadic) * half ^ 14),
        ((-7807 : Dyadic) * half ^ 14)⟩,
       ⟨((8639 : Dyadic) * half ^ 14),
        ((111 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word43Step17 :
    word43Chunk17.foldl (fun acc a => a.applyPacked acc)
      word43State17 = word43State18 := by decide +kernel

private def word43Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word43State19 : PackedMat2 :=
    ⟨⟨⟨((14375 : Dyadic) * half ^ 14),
        ((721 : Dyadic) * half ^ 15)⟩,
       ⟨((1889 : Dyadic) * half ^ 14),
        ((-3739 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1185 : Dyadic) * half ^ 13),
        ((1261 : Dyadic) * half ^ 15)⟩,
       ⟨((3321 : Dyadic) * half ^ 13),
        ((-947 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1185 : Dyadic) * half ^ 13),
        ((1261 : Dyadic) * half ^ 15)⟩,
       ⟨((-3321 : Dyadic) * half ^ 13),
        ((947 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-14375 : Dyadic) * half ^ 14),
        ((-721 : Dyadic) * half ^ 15)⟩,
       ⟨((1889 : Dyadic) * half ^ 14),
        ((-3739 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word43Step18 :
    word43Chunk18.foldl (fun acc a => a.applyPacked acc)
      word43State18 = word43State19 := by decide +kernel

private def word43Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word43State20 : PackedMat2 :=
    ⟨⟨⟨((-1011 : Dyadic) * half ^ 15),
        ((41501 : Dyadic) * half ^ 16)⟩,
       ⟨((2935 : Dyadic) * half ^ 13),
        ((227 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-121 : Dyadic) * half ^ 10),
        ((-10577 : Dyadic) * half ^ 16)⟩,
       ⟨((-807 : Dyadic) * half ^ 15),
        ((2059 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-807 : Dyadic) * half ^ 15),
        ((2059 : Dyadic) * half ^ 16)⟩,
       ⟨((-121 : Dyadic) * half ^ 10),
        ((-10577 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2935 : Dyadic) * half ^ 13),
        ((-227 : Dyadic) * half ^ 16)⟩,
       ⟨((1011 : Dyadic) * half ^ 15),
        ((-41501 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word43Step19 :
    word43Chunk19.foldl (fun acc a => a.applyPacked acc)
      word43State19 = word43State20 := by decide +kernel

private def word43Chunk20 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word43State21 : PackedMat2 :=
    ⟨⟨⟨((-4551 : Dyadic) * half ^ 16),
        ((50011 : Dyadic) * half ^ 17)⟩,
       ⟨((4669 : Dyadic) * half ^ 13),
        ((12955 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((1119 : Dyadic) * half ^ 13),
        ((-37963 : Dyadic) * half ^ 17)⟩,
       ⟨((-2173 : Dyadic) * half ^ 16),
        ((-38449 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((243 : Dyadic) * half ^ 16),
        ((11125 : Dyadic) * half ^ 17)⟩,
       ⟨((19103 : Dyadic) * half ^ 15),
        ((-6779 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-579 : Dyadic) * half ^ 11),
        ((41903 : Dyadic) * half ^ 17)⟩,
       ⟨((31483 : Dyadic) * half ^ 16),
        ((32801 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word43Step20 :
    word43Chunk20.foldl (fun acc a => a.applyPacked acc)
      word43State20 = word43State21 := by decide +kernel

private def word43Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word43State22 : PackedMat2 :=
    ⟨⟨⟨((1879 : Dyadic) * half ^ 14),
        ((-38577 : Dyadic) * half ^ 18)⟩,
       ⟨((93275 : Dyadic) * half ^ 17),
        ((50101 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((18803 : Dyadic) * half ^ 17),
        ((-38885 : Dyadic) * half ^ 18)⟩,
       ⟨((-623 : Dyadic) * half ^ 11),
        ((84323 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((15401 : Dyadic) * half ^ 15),
        ((-58675 : Dyadic) * half ^ 18)⟩,
       ⟨((22719 : Dyadic) * half ^ 17),
        ((-21069 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-44339 : Dyadic) * half ^ 17),
        ((-78243 : Dyadic) * half ^ 18)⟩,
       ⟨((-2881 : Dyadic) * half ^ 16),
        ((-108307 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word43Step21 :
    word43Chunk21.foldl (fun acc a => a.applyPacked acc)
      word43State21 = word43State22 := by decide +kernel

private def word43Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word43State23 : PackedMat2 :=
    ⟨⟨⟨((-2975 : Dyadic) * half ^ 13),
        ((20349 : Dyadic) * half ^ 18)⟩,
       ⟨((107125 : Dyadic) * half ^ 17),
        ((7773 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((21789 : Dyadic) * half ^ 16),
        ((-17985 : Dyadic) * half ^ 18)⟩,
       ⟨((-951 : Dyadic) * half ^ 16),
        ((-11435 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((63725 : Dyadic) * half ^ 18),
        ((-10419 : Dyadic) * half ^ 16)⟩,
       ⟨((-27755 : Dyadic) * half ^ 18),
        ((-5685 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((35895 : Dyadic) * half ^ 18),
        ((59525 : Dyadic) * half ^ 18)⟩,
       ⟨((4803 : Dyadic) * half ^ 18),
        ((-154725 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word43Step22 :
    word43Chunk22.foldl (fun acc a => a.applyPacked acc)
      word43State22 = word43State23 := by decide +kernel

private def word43Chunk23 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word43State24 : PackedMat2 :=
    ⟨⟨⟨((25091 : Dyadic) * half ^ 19),
        ((-127809 : Dyadic) * half ^ 18)⟩,
       ⟨((119749 : Dyadic) * half ^ 19),
        ((-391 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((195045 : Dyadic) * half ^ 19),
        ((-14133 : Dyadic) * half ^ 19)⟩,
       ⟨((-297461 : Dyadic) * half ^ 19),
        ((-33347 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-5935 : Dyadic) * half ^ 16),
        ((-6401 : Dyadic) * half ^ 16)⟩,
       ⟨((9607 : Dyadic) * half ^ 18),
        ((246253 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((130937 : Dyadic) * half ^ 18),
        ((-18105 : Dyadic) * half ^ 17)⟩,
       ⟨((124681 : Dyadic) * half ^ 18),
        ((47329 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word43Step23 :
    word43Chunk23.foldl (fun acc a => a.applyPacked acc)
      word43State23 = word43State24 := by decide +kernel

private def word43Chunk24 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word43State25 : PackedMat2 :=
    ⟨⟨⟨((-678465 : Dyadic) * half ^ 20),
        ((-19861 : Dyadic) * half ^ 20)⟩,
       ⟨((31793 : Dyadic) * half ^ 20),
        ((6899 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((531069 : Dyadic) * half ^ 20),
        ((38993 : Dyadic) * half ^ 18)⟩,
       ⟨((377713 : Dyadic) * half ^ 20),
        ((-264265 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-531069 : Dyadic) * half ^ 20),
        ((-38993 : Dyadic) * half ^ 18)⟩,
       ⟨((377713 : Dyadic) * half ^ 20),
        ((-264265 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-678465 : Dyadic) * half ^ 20),
        ((-19861 : Dyadic) * half ^ 20)⟩,
       ⟨((-31793 : Dyadic) * half ^ 20),
        ((-6899 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word43Step24 :
    word43Chunk24.foldl (fun acc a => a.applyPacked acc)
      word43State24 = word43State25 := by decide +kernel

private def word43Chunk25 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word43State26 : PackedMat2 :=
    ⟨⟨⟨((229777 : Dyadic) * half ^ 20),
        ((-632877 : Dyadic) * half ^ 21)⟩,
       ⟨((-417705 : Dyadic) * half ^ 20),
        ((276197 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((76587 : Dyadic) * half ^ 18),
        ((815195 : Dyadic) * half ^ 21)⟩,
       ⟨((8583 : Dyadic) * half ^ 19),
        ((644069 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((85563 : Dyadic) * half ^ 20),
        ((144591 : Dyadic) * half ^ 20)⟩,
       ⟨((-22801 : Dyadic) * half ^ 15),
        ((-161757 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((454537 : Dyadic) * half ^ 20),
        ((-323741 : Dyadic) * half ^ 20)⟩,
       ⟨((-44585 : Dyadic) * half ^ 18),
        ((-23491 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word43Step25 :
    word43Chunk25.foldl (fun acc a => a.applyPacked acc)
      word43State25 = word43State26 := by decide +kernel

private def word43Chunk26 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word43State27 : PackedMat2 :=
    ⟨⟨⟨((-300735 : Dyadic) * half ^ 21),
        ((-105825 : Dyadic) * half ^ 22)⟩,
       ⟨((617803 : Dyadic) * half ^ 20),
        ((-1144773 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((85873 : Dyadic) * half ^ 19),
        ((616109 : Dyadic) * half ^ 22)⟩,
       ⟨((1128757 : Dyadic) * half ^ 21),
        ((1037455 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1128757 : Dyadic) * half ^ 21),
        ((1037455 : Dyadic) * half ^ 22)⟩,
       ⟨((85873 : Dyadic) * half ^ 19),
        ((616109 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-617803 : Dyadic) * half ^ 20),
        ((1144773 : Dyadic) * half ^ 22)⟩,
       ⟨((300735 : Dyadic) * half ^ 21),
        ((105825 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word43Step26 :
    word43Chunk26.foldl (fun acc a => a.applyPacked acc)
      word43State26 = word43State27 := by decide +kernel

private def word43Chunk27 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word43State28 : PackedMat2 :=
    ⟨⟨⟨((2253157 : Dyadic) * half ^ 22),
        ((-956269 : Dyadic) * half ^ 23)⟩,
       ⟨((1156801 : Dyadic) * half ^ 21),
        ((1751439 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-459823 : Dyadic) * half ^ 20),
        ((1061537 : Dyadic) * half ^ 23)⟩,
       ⟨((1106373 : Dyadic) * half ^ 22),
        ((49683 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((505927 : Dyadic) * half ^ 22),
        ((-2945665 : Dyadic) * half ^ 23)⟩,
       ⟨((-277805 : Dyadic) * half ^ 21),
        ((732919 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((676927 : Dyadic) * half ^ 21),
        ((60445 : Dyadic) * half ^ 23)⟩,
       ⟨((397585 : Dyadic) * half ^ 22),
        ((4566759 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word43Step27 :
    word43Chunk27.foldl (fun acc a => a.applyPacked acc)
      word43State27 = word43State28 := by decide +kernel

private def word43Chunk28 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word43State29 : PackedMat2 :=
    ⟨⟨⟨((-1094061 : Dyadic) * half ^ 21),
        ((338149 : Dyadic) * half ^ 21)⟩,
       ⟨((365243 : Dyadic) * half ^ 19),
        ((1304699 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1134383 : Dyadic) * half ^ 22),
        ((-494207 : Dyadic) * half ^ 22)⟩,
       ⟨((115887 : Dyadic) * half ^ 21),
        ((1159007 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((115887 : Dyadic) * half ^ 21),
        ((1159007 : Dyadic) * half ^ 23)⟩,
       ⟨((1134383 : Dyadic) * half ^ 22),
        ((-494207 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-365243 : Dyadic) * half ^ 19),
        ((-1304699 : Dyadic) * half ^ 23)⟩,
       ⟨((1094061 : Dyadic) * half ^ 21),
        ((-338149 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word43Step28 :
    word43Chunk28.foldl (fun acc a => a.applyPacked acc)
      word43State28 = word43State29 := by decide +kernel

private def word43Chunk29 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word43State30 : PackedMat2 :=
    ⟨⟨⟨((-9831603 : Dyadic) * half ^ 24),
        ((1770133 : Dyadic) * half ^ 24)⟩,
       ⟨((1883295 : Dyadic) * half ^ 24),
        ((278949 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-2400433 : Dyadic) * half ^ 24),
        ((142833 : Dyadic) * half ^ 22)⟩,
       ⟨((-964153 : Dyadic) * half ^ 24),
        ((-2036715 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2400433 : Dyadic) * half ^ 24),
        ((-142833 : Dyadic) * half ^ 22)⟩,
       ⟨((-964153 : Dyadic) * half ^ 24),
        ((-2036715 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-9831603 : Dyadic) * half ^ 24),
        ((1770133 : Dyadic) * half ^ 24)⟩,
       ⟨((-1883295 : Dyadic) * half ^ 24),
        ((-278949 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word43Step29 :
    word43Chunk29.foldl (fun acc a => a.applyPacked acc)
      word43State29 = word43State30 := by decide +kernel

private def word43Chunk30 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word43State31 : PackedMat2 :=
    ⟨⟨⟨((-19909949 : Dyadic) * half ^ 25),
        ((-1554653 : Dyadic) * half ^ 25)⟩,
       ⟨((14605075 : Dyadic) * half ^ 25),
        ((-3263303 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1124847 : Dyadic) * half ^ 25),
        ((-4731337 : Dyadic) * half ^ 24)⟩,
       ⟨((-5128125 : Dyadic) * half ^ 25),
        ((-10476431 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1124847 : Dyadic) * half ^ 25),
        ((-4731337 : Dyadic) * half ^ 24)⟩,
       ⟨((5128125 : Dyadic) * half ^ 25),
        ((10476431 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((19909949 : Dyadic) * half ^ 25),
        ((1554653 : Dyadic) * half ^ 25)⟩,
       ⟨((14605075 : Dyadic) * half ^ 25),
        ((-3263303 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word43Step30 :
    word43Chunk30.foldl (fun acc a => a.applyPacked acc)
      word43State30 = word43State31 := by decide +kernel

private def word43Chunk31 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word43State32 : PackedMat2 :=
    ⟨⟨⟨((1411323 : Dyadic) * half ^ 23),
        ((-3587307 : Dyadic) * half ^ 25)⟩,
       ⟨((-11328589 : Dyadic) * half ^ 25),
        ((2723001 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((286847 : Dyadic) * half ^ 23),
        ((2449891 : Dyadic) * half ^ 22)⟩,
       ⟨((-12008543 : Dyadic) * half ^ 25),
        ((-2382583 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-21981711 : Dyadic) * half ^ 25),
        ((-13155931 : Dyadic) * half ^ 26)⟩,
       ⟨((17216545 : Dyadic) * half ^ 25),
        ((-10861155 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-1577577 : Dyadic) * half ^ 23),
        ((16973881 : Dyadic) * half ^ 26)⟩,
       ⟨((432153 : Dyadic) * half ^ 24),
        ((5683297 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word43Step31 :
    word43Chunk31.foldl (fun acc a => a.applyPacked acc)
      word43State31 = word43State32 := by decide +kernel

private def word43Chunk32 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word43State33 : PackedMat2 :=
    ⟨⟨⟨((-10417753 : Dyadic) * half ^ 25),
        ((-3276045 : Dyadic) * half ^ 26)⟩,
       ⟨((1229997 : Dyadic) * half ^ 26),
        ((6159059 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3087207 : Dyadic) * half ^ 23),
        ((11849825 : Dyadic) * half ^ 25)⟩,
       ⟨((36666663 : Dyadic) * half ^ 26),
        ((-2279779 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((20968941 : Dyadic) * half ^ 25),
        ((-11969007 : Dyadic) * half ^ 27)⟩,
       ⟨((-2730709 : Dyadic) * half ^ 25),
        ((-61364319 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((15594163 : Dyadic) * half ^ 26),
        ((22065503 : Dyadic) * half ^ 27)⟩,
       ⟨((9042073 : Dyadic) * half ^ 26),
        ((-19605509 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word43Step32 :
    word43Chunk32.foldl (fun acc a => a.applyPacked acc)
      word43State32 = word43State33 := by decide +kernel

private def word43Chunk33 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word43State34 : PackedMat2 :=
    ⟨⟨⟨((-49719969 : Dyadic) * half ^ 27),
        ((-54338241 : Dyadic) * half ^ 28)⟩,
       ⟨((2315537 : Dyadic) * half ^ 25),
        ((57272223 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-2430763 : Dyadic) * half ^ 26),
        ((63806273 : Dyadic) * half ^ 28)⟩,
       ⟨((-20820881 : Dyadic) * half ^ 27),
        ((140338135 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-20820881 : Dyadic) * half ^ 27),
        ((140338135 : Dyadic) * half ^ 28)⟩,
       ⟨((-2430763 : Dyadic) * half ^ 26),
        ((63806273 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-2315537 : Dyadic) * half ^ 25),
        ((-57272223 : Dyadic) * half ^ 28)⟩,
       ⟨((49719969 : Dyadic) * half ^ 27),
        ((54338241 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word43Step33 :
    word43Chunk33.foldl (fun acc a => a.applyPacked acc)
      word43State33 = word43State34 := by decide +kernel

private def word43Chunk34 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word43State35 : PackedMat2 :=
    ⟨⟨⟨((46728773 : Dyadic) * half ^ 28),
        ((57496811 : Dyadic) * half ^ 29)⟩,
       ⟨((36069239 : Dyadic) * half ^ 26),
        ((-62724601 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-9201419 : Dyadic) * half ^ 24),
        ((53181829 : Dyadic) * half ^ 29)⟩,
       ⟨((79116647 : Dyadic) * half ^ 28),
        ((179387427 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-63102799 : Dyadic) * half ^ 28),
        ((-226339351 : Dyadic) * half ^ 29)⟩,
       ⟨((-29071157 : Dyadic) * half ^ 26),
        ((68106057 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-30055353 : Dyadic) * half ^ 27),
        ((97548183 : Dyadic) * half ^ 29)⟩,
       ⟨((-2613895 : Dyadic) * half ^ 28),
        ((191005729 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word43Step34 :
    word43Chunk34.foldl (fun acc a => a.applyPacked acc)
      word43State34 = word43State35 := by decide +kernel

private def word43Chunk35 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word43State36 : PackedMat2 :=
    ⟨⟨⟨((60442559 : Dyadic) * half ^ 29),
        ((51500159 : Dyadic) * half ^ 29)⟩,
       ⟨((63120819 : Dyadic) * half ^ 29),
        ((262719075 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((20793955 : Dyadic) * half ^ 29),
        ((-52042003 : Dyadic) * half ^ 27)⟩,
       ⟨((-112112233 : Dyadic) * half ^ 29),
        ((68534931 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-35549075 : Dyadic) * half ^ 28),
        ((-45659139 : Dyadic) * half ^ 29)⟩,
       ⟨((-172618937 : Dyadic) * half ^ 28),
        ((33226547 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-157109617 : Dyadic) * half ^ 28),
        ((-61781689 : Dyadic) * half ^ 29)⟩,
       ⟨((52804729 : Dyadic) * half ^ 27),
        ((669565 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word43Step35 :
    word43Chunk35.foldl (fun acc a => a.applyPacked acc)
      word43State35 = word43State36 := by decide +kernel

private def word43Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word43State37 : PackedMat2 :=
    ⟨⟨⟨((-283438385 : Dyadic) * half ^ 29),
        ((59366743 : Dyadic) * half ^ 28)⟩,
       ⟨((754119 : Dyadic) * half ^ 28),
        ((-188900095 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-89782917 : Dyadic) * half ^ 28),
        ((-214771465 : Dyadic) * half ^ 29)⟩,
       ⟨((-17751365 : Dyadic) * half ^ 28),
        ((268685623 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((17751365 : Dyadic) * half ^ 28),
        ((-268685623 : Dyadic) * half ^ 30)⟩,
       ⟨((89782917 : Dyadic) * half ^ 28),
        ((214771465 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((754119 : Dyadic) * half ^ 28),
        ((-188900095 : Dyadic) * half ^ 30)⟩,
       ⟨((-283438385 : Dyadic) * half ^ 29),
        ((59366743 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word43Step36 :
    word43Chunk36.foldl (fun acc a => a.applyPacked acc)
      word43State36 = word43State37 := by decide +kernel

private def word43Chunk37 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word43State38 : PackedMat2 :=
    ⟨⟨⟨((-567716311 : Dyadic) * half ^ 30),
        ((-125214375 : Dyadic) * half ^ 31)⟩,
       ⟨((-98919775 : Dyadic) * half ^ 30),
        ((-886595445 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((80008883 : Dyadic) * half ^ 29),
        ((-170011191 : Dyadic) * half ^ 31)⟩,
       ⟨((-298146151 : Dyadic) * half ^ 29),
        ((220669047 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-195340119 : Dyadic) * half ^ 30),
        ((189077517 : Dyadic) * half ^ 29)⟩,
       ⟨((-791529 : Dyadic) * half ^ 25),
        ((54534317 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-380690535 : Dyadic) * half ^ 30),
        ((58599567 : Dyadic) * half ^ 28)⟩,
       ⟨((-252952455 : Dyadic) * half ^ 29),
        ((-333318043 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word43Step37 :
    word43Chunk37.foldl (fun acc a => a.applyPacked acc)
      word43State37 = word43State38 := by decide +kernel

private def word43Chunk38 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word43State39 : PackedMat2 :=
    ⟨⟨⟨((758490725 : Dyadic) * half ^ 31),
        ((-29676843 : Dyadic) * half ^ 28)⟩,
       ⟨((-15485483 : Dyadic) * half ^ 30),
        ((-900194813 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-732711365 : Dyadic) * half ^ 31),
        ((224580247 : Dyadic) * half ^ 30)⟩,
       ⟨((-208439233 : Dyadic) * half ^ 29),
        ((-72158617 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((732711365 : Dyadic) * half ^ 31),
        ((-224580247 : Dyadic) * half ^ 30)⟩,
       ⟨((-208439233 : Dyadic) * half ^ 29),
        ((-72158617 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((758490725 : Dyadic) * half ^ 31),
        ((-29676843 : Dyadic) * half ^ 28)⟩,
       ⟨((15485483 : Dyadic) * half ^ 30),
        ((900194813 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word43Step38 :
    word43Chunk38.foldl (fun acc a => a.applyPacked acc)
      word43State38 = word43State39 := by decide +kernel

private def word43Chunk39 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word43State40 : PackedMat2 :=
    ⟨⟨⟨((242804533 : Dyadic) * half ^ 31),
        ((3207617769 : Dyadic) * half ^ 33)⟩,
       ⟨((797451055 : Dyadic) * half ^ 32),
        ((-3963001793 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-58033841 : Dyadic) * half ^ 32),
        ((-1313999063 : Dyadic) * half ^ 33)⟩,
       ⟨((-917203501 : Dyadic) * half ^ 31),
        ((-832091939 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((917203501 : Dyadic) * half ^ 31),
        ((832091939 : Dyadic) * half ^ 33)⟩,
       ⟨((58033841 : Dyadic) * half ^ 32),
        ((1313999063 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((797451055 : Dyadic) * half ^ 32),
        ((-3963001793 : Dyadic) * half ^ 33)⟩,
       ⟨((242804533 : Dyadic) * half ^ 31),
        ((3207617769 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word43Step39 :
    word43Chunk39.foldl (fun acc a => a.applyPacked acc)
      word43State39 = word43State40 := by decide +kernel

private def word43Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word43State41 : PackedMat2 :=
    ⟨⟨⟨((3375295161 : Dyadic) * half ^ 33),
        ((1167991439 : Dyadic) * half ^ 33)⟩,
       ⟨((-448580439 : Dyadic) * half ^ 33),
        ((3338653261 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1273795269 : Dyadic) * half ^ 33),
        ((1301381071 : Dyadic) * half ^ 32)⟩,
       ⟨((4288637441 : Dyadic) * half ^ 33),
        ((-671547489 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((314916791 : Dyadic) * half ^ 31),
        ((2781216355 : Dyadic) * half ^ 33)⟩,
       ⟨((123308035 : Dyadic) * half ^ 28),
        ((-753710543 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1126661175 : Dyadic) * half ^ 31),
        ((-1463357361 : Dyadic) * half ^ 33)⟩,
       ⟨((1085330911 : Dyadic) * half ^ 32),
        ((-238992225 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word43Step40 :
    word43Chunk40.foldl (fun acc a => a.applyPacked acc)
      word43State40 = word43State41 := by decide +kernel

private def word43Chunk41 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word43State42 : PackedMat2 :=
    ⟨⟨⟨((-3823581275 : Dyadic) * half ^ 34),
        ((4027621 : Dyadic) * half ^ 33)⟩,
       ⟨((4041882859 : Dyadic) * half ^ 34),
        ((635790517 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4991870751 : Dyadic) * half ^ 34),
        ((-3935079689 : Dyadic) * half ^ 34)⟩,
       ⟨((-2203755447 : Dyadic) * half ^ 34),
        ((629107921 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-6130647047 : Dyadic) * half ^ 34),
        ((3597813099 : Dyadic) * half ^ 34)⟩,
       ⟨((14000806425 : Dyadic) * half ^ 34),
        ((348514413 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((643845759 : Dyadic) * half ^ 34),
        ((13643849 : Dyadic) * half ^ 31)⟩,
       ⟨((-627735275 : Dyadic) * half ^ 34),
        ((-3932732067 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word43Step41 :
    word43Chunk41.foldl (fun acc a => a.applyPacked acc)
      word43State41 = word43State42 := by decide +kernel

private def word43Chunk42 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word43State43 : PackedMat2 :=
    ⟨⟨⟨((-3488341953 : Dyadic) * half ^ 34),
        ((-978764727 : Dyadic) * half ^ 35)⟩,
       ⟨((3389594025 : Dyadic) * half ^ 34),
        ((875473169 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1540333617 : Dyadic) * half ^ 33),
        ((-7415553907 : Dyadic) * half ^ 35)⟩,
       ⟨((678699117 : Dyadic) * half ^ 33),
        ((-21531351591 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1540333617 : Dyadic) * half ^ 33),
        ((-7415553907 : Dyadic) * half ^ 35)⟩,
       ⟨((-678699117 : Dyadic) * half ^ 33),
        ((21531351591 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3488341953 : Dyadic) * half ^ 34),
        ((978764727 : Dyadic) * half ^ 35)⟩,
       ⟨((3389594025 : Dyadic) * half ^ 34),
        ((875473169 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word43Step42 :
    word43Chunk42.foldl (fun acc a => a.applyPacked acc)
      word43State42 = word43State43 := by decide +kernel

private def word43Chunk43 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word43State44 : PackedMat2 :=
    ⟨⟨⟨((-5713128797 : Dyadic) * half ^ 34),
        ((-3414091607 : Dyadic) * half ^ 36)⟩,
       ⟨((-17086321533 : Dyadic) * half ^ 35),
        ((4077154323 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-9700071089 : Dyadic) * half ^ 35),
        ((8492081145 : Dyadic) * half ^ 36)⟩,
       ⟨((-12280186523 : Dyadic) * half ^ 34),
        ((-4602009511 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-409190333 : Dyadic) * half ^ 31),
        ((-14860301957 : Dyadic) * half ^ 36)⟩,
       ⟨((1945035817 : Dyadic) * half ^ 35),
        ((-34260444135 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-3745622965 : Dyadic) * half ^ 35),
        ((5660063939 : Dyadic) * half ^ 36)⟩,
       ⟨((-165765679 : Dyadic) * half ^ 34),
        ((28512579127 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word43Step43 :
    word43Chunk43.foldl (fun acc a => a.applyPacked acc)
      word43State43 = word43State44 := by decide +kernel

private def word43Chunk44 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word43State45 : PackedMat2 :=
    ⟨⟨⟨((505819935 : Dyadic) * half ^ 33),
        ((-871690461 : Dyadic) * half ^ 36)⟩,
       ⟨((-15657000745 : Dyadic) * half ^ 35),
        ((-4964325795 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4284217283 : Dyadic) * half ^ 34),
        ((-24839466303 : Dyadic) * half ^ 36)⟩,
       ⟨((-11138278107 : Dyadic) * half ^ 34),
        ((-331885399 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((27494549495 : Dyadic) * half ^ 36),
        ((856757603 : Dyadic) * half ^ 32)⟩,
       ⟨((22184383111 : Dyadic) * half ^ 36),
        ((-7711247695 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-10800342051 : Dyadic) * half ^ 36),
        ((-13633721005 : Dyadic) * half ^ 36)⟩,
       ⟨((9056961129 : Dyadic) * half ^ 36),
        ((17680280485 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word43Step44 :
    word43Chunk44.foldl (fun acc a => a.applyPacked acc)
      word43State44 = word43State45 := by decide +kernel

private def word43Chunk45 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word43State46 : PackedMat2 :=
    ⟨⟨⟨((19848907741 : Dyadic) * half ^ 35),
        ((18090753093 : Dyadic) * half ^ 37)⟩,
       ⟨((-34594457025 : Dyadic) * half ^ 36),
        ((2787475205 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-14218112853 : Dyadic) * half ^ 35),
        ((-4776261409 : Dyadic) * half ^ 37)⟩,
       ⟨((-3003620691 : Dyadic) * half ^ 34),
        ((19487208485 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-3003620691 : Dyadic) * half ^ 34),
        ((19487208485 : Dyadic) * half ^ 36)⟩,
       ⟨((-14218112853 : Dyadic) * half ^ 35),
        ((-4776261409 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((34594457025 : Dyadic) * half ^ 36),
        ((-2787475205 : Dyadic) * half ^ 35)⟩,
       ⟨((-19848907741 : Dyadic) * half ^ 35),
        ((-18090753093 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word43Step45 :
    word43Chunk45.foldl (fun acc a => a.applyPacked acc)
      word43State45 = word43State46 := by decide +kernel

private def word43Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word43State47 : PackedMat2 :=
    ⟨⟨⟨((71172264675 : Dyadic) * half ^ 38),
        ((54348219307 : Dyadic) * half ^ 37)⟩,
       ⟨((145446110983 : Dyadic) * half ^ 38),
        ((-34676418015 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((43717096623 : Dyadic) * half ^ 38),
        ((-90743509925 : Dyadic) * half ^ 38)⟩,
       ⟨((28017234801 : Dyadic) * half ^ 38),
        ((22743522785 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((45256464355 : Dyadic) * half ^ 38),
        ((-2241697857 : Dyadic) * half ^ 34)⟩,
       ⟨((136230555495 : Dyadic) * half ^ 38),
        ((-7849930911 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((74020020599 : Dyadic) * half ^ 38),
        ((108309187829 : Dyadic) * half ^ 38)⟩,
       ⟨((143372856629 : Dyadic) * half ^ 38),
        ((-18568461577 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word43Step46 :
    word43Chunk46.foldl (fun acc a => a.applyPacked acc)
      word43State46 = word43State47 := by decide +kernel

private def word43Chunk47 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word43State48 : PackedMat2 :=
    ⟨⟨⟨((14114834811 : Dyadic) * half ^ 38),
        ((196592192615 : Dyadic) * half ^ 39)⟩,
       ⟨((14918331723 : Dyadic) * half ^ 38),
        ((299629595167 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-17291498747 : Dyadic) * half ^ 36),
        ((106926489667 : Dyadic) * half ^ 39)⟩,
       ⟨((-2688730805 : Dyadic) * half ^ 37),
        ((-28049857109 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-17291498747 : Dyadic) * half ^ 36),
        ((106926489667 : Dyadic) * half ^ 39)⟩,
       ⟨((2688730805 : Dyadic) * half ^ 37),
        ((28049857109 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-14114834811 : Dyadic) * half ^ 38),
        ((-196592192615 : Dyadic) * half ^ 39)⟩,
       ⟨((14918331723 : Dyadic) * half ^ 38),
        ((299629595167 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word43Step47 :
    word43Chunk47.foldl (fun acc a => a.applyPacked acc)
      word43State47 = word43State48 := by decide +kernel

private def word43Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word43State49 : PackedMat2 :=
    ⟨⟨⟨((-74858931399 : Dyadic) * half ^ 38),
        ((-390098795027 : Dyadic) * half ^ 40)⟩,
       ⟨((252684858589 : Dyadic) * half ^ 39),
        ((-45954378909 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((127916795175 : Dyadic) * half ^ 39),
        ((-339257358551 : Dyadic) * half ^ 40)⟩,
       ⟨((-147373209 : Dyadic) * half ^ 33),
        ((360062485345 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((87414980487 : Dyadic) * half ^ 37),
        ((-137348680551 : Dyadic) * half ^ 40)⟩,
       ⟨((10402563397 : Dyadic) * half ^ 39),
        ((118484909799 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-172072208059 : Dyadic) * half ^ 39),
        ((-402402721387 : Dyadic) * half ^ 40)⟩,
       ⟨((27253323371 : Dyadic) * half ^ 36),
        ((-102966995791 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word43Step48 :
    word43Chunk48.foldl (fun acc a => a.applyPacked acc)
      word43State48 = word43State49 := by decide +kernel

private def word43Chunk49 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word43State50 : PackedMat2 :=
    ⟨⟨⟨((-970089230303 : Dyadic) * half ^ 40),
        ((-1622324059 : Dyadic) * half ^ 35)⟩,
       ⟨((264636640453 : Dyadic) * half ^ 40),
        ((-38033840587 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((319823452007 : Dyadic) * half ^ 40),
        ((-89216106355 : Dyadic) * half ^ 40)⟩,
       ⟨((250118244779 : Dyadic) * half ^ 40),
        ((-6788278983 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((48002192669 : Dyadic) * half ^ 39),
        ((-284970848393 : Dyadic) * half ^ 40)⟩,
       ⟨((20606956843 : Dyadic) * half ^ 38),
        ((-17426301807 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-63991025531 : Dyadic) * half ^ 39),
        ((-352726294925 : Dyadic) * half ^ 40)⟩,
       ⟨((12076655643 : Dyadic) * half ^ 39),
        ((-308681467689 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word43Step49 :
    word43Chunk49.foldl (fun acc a => a.applyPacked acc)
      word43State49 = word43State50 := by decide +kernel

private def word43Chunk50 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word43State51 : PackedMat2 :=
    ⟨⟨⟨((-693657887269 : Dyadic) * half ^ 40),
        ((-373281674161 : Dyadic) * half ^ 41)⟩,
       ⟨((-53970393967 : Dyadic) * half ^ 38),
        ((-226021003399 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((463456450047 : Dyadic) * half ^ 40),
        ((-752610413225 : Dyadic) * half ^ 41)⟩,
       ⟨((84607186533 : Dyadic) * half ^ 40),
        ((-45594045703 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((84607186533 : Dyadic) * half ^ 40),
        ((-45594045703 : Dyadic) * half ^ 40)⟩,
       ⟨((463456450047 : Dyadic) * half ^ 40),
        ((-752610413225 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((53970393967 : Dyadic) * half ^ 38),
        ((226021003399 : Dyadic) * half ^ 40)⟩,
       ⟨((693657887269 : Dyadic) * half ^ 40),
        ((373281674161 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word43Step50 :
    word43Chunk50.foldl (fun acc a => a.applyPacked acc)
      word43State50 = word43State51 := by decide +kernel

private def word43Chunk51 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word43State52 : PackedMat2 :=
    ⟨⟨⟨((528998308045 : Dyadic) * half ^ 42),
        ((-46354293885 : Dyadic) * half ^ 37)⟩,
       ⟨((-1629977466315 : Dyadic) * half ^ 42),
        ((-1183894089411 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-2499758880475 : Dyadic) * half ^ 42),
        ((108561528363 : Dyadic) * half ^ 42)⟩,
       ⟨((823297049919 : Dyadic) * half ^ 42),
        ((-132646543945 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((952610823197 : Dyadic) * half ^ 42),
        ((419115457639 : Dyadic) * half ^ 41)⟩,
       ⟨((-1169733879923 : Dyadic) * half ^ 42),
        ((1661527965197 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-2667231493731 : Dyadic) * half ^ 42),
        ((-550489579135 : Dyadic) * half ^ 42)⟩,
       ⟨((-299443314909 : Dyadic) * half ^ 42),
        ((269871971795 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word43Step51 :
    word43Chunk51.foldl (fun acc a => a.applyPacked acc)
      word43State51 = word43State52 := by decide +kernel

private def word43Chunk52 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word43State53 : PackedMat2 :=
    ⟨⟨⟨((581530769075 : Dyadic) * half ^ 42),
        ((1604330869093 : Dyadic) * half ^ 43)⟩,
       ⟨((-507746410429 : Dyadic) * half ^ 42),
        ((-4174487222195 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-19293921287 : Dyadic) * half ^ 41),
        ((-2921923933235 : Dyadic) * half ^ 43)⟩,
       ⟨((-93503941165 : Dyadic) * half ^ 38),
        ((2115752667693 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-19293921287 : Dyadic) * half ^ 41),
        ((-2921923933235 : Dyadic) * half ^ 43)⟩,
       ⟨((93503941165 : Dyadic) * half ^ 38),
        ((-2115752667693 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-581530769075 : Dyadic) * half ^ 42),
        ((-1604330869093 : Dyadic) * half ^ 43)⟩,
       ⟨((-507746410429 : Dyadic) * half ^ 42),
        ((-4174487222195 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word43Step52 :
    word43Chunk52.foldl (fun acc a => a.applyPacked acc)
      word43State52 = word43State53 := by decide +kernel

private def word43Chunk53 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word43State54 : PackedMat2 :=
    ⟨⟨⟨((347129605553 : Dyadic) * half ^ 40),
        ((737509599371 : Dyadic) * half ^ 44)⟩,
       ⟨((1300262061593 : Dyadic) * half ^ 43),
        ((3736849782241 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-1565718168325 : Dyadic) * half ^ 43),
        ((659315612515 : Dyadic) * half ^ 44)⟩,
       ⟨((273321586433 : Dyadic) * half ^ 42),
        ((-10746814724337 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-2851532584213 : Dyadic) * half ^ 42),
        ((2112361341191 : Dyadic) * half ^ 44)⟩,
       ⟨((-5043749555911 : Dyadic) * half ^ 43),
        ((-1019074995459 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-1499670091435 : Dyadic) * half ^ 43),
        ((1476774782831 : Dyadic) * half ^ 44)⟩,
       ⟨((-1118589845403 : Dyadic) * half ^ 42),
        ((-4077298906017 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word43Step53 :
    word43Chunk53.foldl (fun acc a => a.applyPacked acc)
      word43State53 = word43State54 := by decide +kernel

private def word43Chunk54 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word43State55 : PackedMat2 :=
    ⟨⟨⟨((1002965706103 : Dyadic) * half ^ 44),
        ((289477073523 : Dyadic) * half ^ 43)⟩,
       ⟨((7060529799531 : Dyadic) * half ^ 44),
        ((-1852195250445 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((2889709284073 : Dyadic) * half ^ 44),
        ((4176443993529 : Dyadic) * half ^ 44)⟩,
       ⟨((-13612794954255 : Dyadic) * half ^ 44),
        ((-992123911997 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-796080020383 : Dyadic) * half ^ 42),
        ((5361542835091 : Dyadic) * half ^ 44)⟩,
       ⟨((-2584283952763 : Dyadic) * half ^ 43),
        ((-2062813029791 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-781359088461 : Dyadic) * half ^ 42),
        ((4031747752817 : Dyadic) * half ^ 44)⟩,
       ⟨((16731815031 : Dyadic) * half ^ 36),
        ((-1514391023357 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word43Step54 :
    word43Chunk54.foldl (fun acc a => a.applyPacked acc)
      word43State54 = word43State55 := by decide +kernel

private def word43Chunk55 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word43State56 : PackedMat2 :=
    ⟨⟨⟨((-9086941586971 : Dyadic) * half ^ 45),
        ((2517224760521 : Dyadic) * half ^ 43)⟩,
       ⟨((-11574383201203 : Dyadic) * half ^ 45),
        ((-611768172587 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((18840246587469 : Dyadic) * half ^ 45),
        ((7913580948887 : Dyadic) * half ^ 45)⟩,
       ⟨((5188806108015 : Dyadic) * half ^ 45),
        ((-779070812965 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((18840246587469 : Dyadic) * half ^ 45),
        ((7913580948887 : Dyadic) * half ^ 45)⟩,
       ⟨((-5188806108015 : Dyadic) * half ^ 45),
        ((779070812965 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((9086941586971 : Dyadic) * half ^ 45),
        ((-2517224760521 : Dyadic) * half ^ 43)⟩,
       ⟨((-11574383201203 : Dyadic) * half ^ 45),
        ((-611768172587 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word43Step55 :
    word43Chunk55.foldl (fun acc a => a.applyPacked acc)
      word43State55 = word43State56 := by decide +kernel

private def word43Chunk56 : List Letter := [.h, .s, .t, .h, .t]
private def word43State57 : PackedMat2 :=
    ⟨⟨⟨((646090252729 : Dyadic) * half ^ 41),
        ((35138862624785 : Dyadic) * half ^ 46)⟩,
       ⟨((-765485017997 : Dyadic) * half ^ 45),
        ((1082559294227 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((10899036509161 : Dyadic) * half ^ 45),
        ((-15413565248055 : Dyadic) * half ^ 46)⟩,
       ⟨((5862566933159 : Dyadic) * half ^ 44),
        ((-16581843334387 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-10899036509161 : Dyadic) * half ^ 45),
        ((15413565248055 : Dyadic) * half ^ 46)⟩,
       ⟨((5862566933159 : Dyadic) * half ^ 44),
        ((-16581843334387 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((646090252729 : Dyadic) * half ^ 41),
        ((35138862624785 : Dyadic) * half ^ 46)⟩,
       ⟨((765485017997 : Dyadic) * half ^ 45),
        ((-1082559294227 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word43Step56 :
    word43Chunk56.foldl (fun acc a => a.applyPacked acc)
      word43State56 = word43State57 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word43_check : check word43 43 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word43 = word43State57.toMatrix := by
    unfold evalRingPacked
    change ((
      word43Chunk0 ++ word43Chunk1 ++ word43Chunk2 ++ word43Chunk3 ++
      word43Chunk4 ++ word43Chunk5 ++ word43Chunk6 ++ word43Chunk7 ++
      word43Chunk8 ++ word43Chunk9 ++ word43Chunk10 ++ word43Chunk11 ++
      word43Chunk12 ++ word43Chunk13 ++ word43Chunk14 ++ word43Chunk15 ++
      word43Chunk16 ++ word43Chunk17 ++ word43Chunk18 ++ word43Chunk19 ++
      word43Chunk20 ++ word43Chunk21 ++ word43Chunk22 ++ word43Chunk23 ++
      word43Chunk24 ++ word43Chunk25 ++ word43Chunk26 ++ word43Chunk27 ++
      word43Chunk28 ++ word43Chunk29 ++ word43Chunk30 ++ word43Chunk31 ++
      word43Chunk32 ++ word43Chunk33 ++ word43Chunk34 ++ word43Chunk35 ++
      word43Chunk36 ++ word43Chunk37 ++ word43Chunk38 ++ word43Chunk39 ++
      word43Chunk40 ++ word43Chunk41 ++ word43Chunk42 ++ word43Chunk43 ++
      word43Chunk44 ++ word43Chunk45 ++ word43Chunk46 ++ word43Chunk47 ++
      word43Chunk48 ++ word43Chunk49 ++ word43Chunk50 ++ word43Chunk51 ++
      word43Chunk52 ++ word43Chunk53 ++ word43Chunk54 ++ word43Chunk55 ++
      word43Chunk56
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word43Step0, word43Step1, word43Step2, word43Step3, word43Step4,
      word43Step5, word43Step6, word43Step7, word43Step8, word43Step9,
      word43Step10, word43Step11, word43Step12, word43Step13, word43Step14,
      word43Step15, word43Step16, word43Step17, word43Step18, word43Step19,
      word43Step20, word43Step21, word43Step22, word43Step23, word43Step24,
      word43Step25, word43Step26, word43Step27, word43Step28, word43Step29,
      word43Step30, word43Step31, word43Step32, word43Step33, word43Step34,
      word43Step35, word43Step36, word43Step37, word43Step38, word43Step39,
      word43Step40, word43Step41, word43Step42, word43Step43, word43Step44,
      word43Step45, word43Step46, word43Step47, word43Step48, word43Step49,
      word43Step50, word43Step51, word43Step52, word43Step53, word43Step54,
      word43Step55, word43Step56]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
