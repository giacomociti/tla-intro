---- MODULE semaphore ----
(*
additional options to generate a dot file:

    -dump dot;colorize ${modelName}.dot
*)
-------------------------------------------------------------------

\* the state of the system
VARIABLE color

\* the expected variable values
TypeOK == color \in {"red", "green", "yellow"}

\* state predicate to describe the initial states
Init == color = "red"


\* action formulas, relating states with the next ones

TurnGreen ==
    /\ color = "red"
    /\ color' = "green"

TurnYellow ==
    /\ color = "green"
    /\ color' = "yellow"

TurnRed ==
    /\ color = "yellow"
    /\ color' = "red"

Next ==
    \/ TurnGreen
    \/ TurnYellow
    \/ TurnRed

\* stardard form to describe the allowed behaviors
Safety == Init /\ [] [Next]_color

\* weak fairness expresses progress requirements
Liveness == WF_color(Next)

\* every specification can be expressed as the conjunction
\* of a safety property and a liveness property
Spec == Safety /\ Liveness

\* additional property implied by Spec (thanks to fairness)
EventuallyGreen == []<> (color = "green")

====
