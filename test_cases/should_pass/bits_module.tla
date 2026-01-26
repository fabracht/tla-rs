---- MODULE bits_module ----
EXTENDS Bits

VARIABLES x

Init == x = 0

Next == x' = x

TestBitAnd == BitAnd(5, 3) = 1 /\ BitAnd(7, 4) = 4 /\ BitAnd(0, 255) = 0

TestBitOr == BitOr(5, 3) = 7 /\ BitOr(0, 8) = 8

TestBitXor == BitXor(5, 3) = 6 /\ BitXor(7, 7) = 0

TestBitNot == BitNot(0) = -1

TestShiftLeft == ShiftLeft(1, 3) = 8 /\ ShiftLeft(5, 0) = 5 /\ LeftShift(1, 4) = 16

TestShiftRight == ShiftRight(16, 2) = 4 /\ ShiftRight(8, 0) = 8 /\ RightShift(32, 3) = 4

Inv == TestBitAnd /\ TestBitOr /\ TestBitXor /\ TestBitNot /\ TestShiftLeft /\ TestShiftRight
====
