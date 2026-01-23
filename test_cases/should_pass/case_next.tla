VARIABLES state

Init == state = "start"

Next ==
    CASE state = "start" -> state' = "middle"
      [] state = "middle" -> state' = "end"
      [] OTHER -> state' = state

Inv == state \in {"start", "middle", "end"}
