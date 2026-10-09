---- MODULE string_sequence_operators ----
EXTENDS Integers, Sequences
VARIABLE id
Prefix(s, n) == SubSeq(s, 1, n)
Init == id = "work-1"
Next == Len(id) < 8 /\ id' = id \o "x"
Lengths == /\ Len(id) \in 6..8
           /\ Len("") = 0
           /\ Len("héllo") = 5
Slices == /\ Prefix(id, 4) = "work"
          /\ SubSeq(id, 6, Len(id)) \in {"1", "1x", "1xx"}
          /\ SubSeq(id, 3, 2) = ""
          /\ SubSeq(id, 9, 2) = ""
          /\ SubSeq(<<1, 2, 3>>, 9, 2) = <<>>
Tails == /\ Tail("a") = ""
         /\ Len(Tail(id)) = Len(id) - 1
         /\ Tail(Tail(id)) \o "!" = SubSeq(id, 3, Len(id)) \o "!"
Concats == /\ "" \o "" = ""
           /\ "work" \o SubSeq(id, 5, Len(id)) = id
Utf16Units == /\ Len("😀") = 2
              /\ Len("a😀b") = 4
              /\ Len(Tail("😀a")) = 2
              /\ SubSeq("😀b", 3, 3) = "b"
              /\ SubSeq("a😀b", 2, 3) = "😀"
              /\ Len(SubSeq("😀b", 1, 1)) = 1
              /\ Len("😀" \o "😀") = 4
====
