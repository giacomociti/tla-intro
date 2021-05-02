---- MODULE spec ----

\* High level description of a system persisting messages in two distinct databases
-----------------------------------------------------------------------------------

\* the set of all possible messages
CONSTANT Message

VARIABLE db1
VARIABLE db2

\* the tuple of all variables
vars == <<db1, db2>>

\* one message chosen as default value
default == CHOOSE m \in Message: TRUE

TypeOK ==
    /\ db1 \in Message
    /\ db2 \in Message

Init ==
    /\ db1 = default
    /\ db2 = default

\* the first consumer step is to persist a received message in the first database
Write1 == \E m \in Message \ {default}:
    /\ db1' = m
    /\ UNCHANGED db2

\* the second consumer step is to align the second database
Write2 ==
    /\ db2' = db1
    /\ UNCHANGED db1

Next ==
    \/ Write1
    \/ Write2

\* the second step must eventally occur in order to guarantee the consistency of the two databases
Liveness == WF_vars(Write2)

Spec == Init /\ [][Next]_vars /\ Liveness

\* in every state (always) the two database values are (or eventually will be) the same
DbConsistency == []<>(db2 = db1)
====
