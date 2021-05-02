---- MODULE design ----

\* Design of a system persisting messages in two distinct databases
-------------------------------------------------------------------


CONSTANT Message \* the set of all possible messages
CONSTANT Process \* a set of consumer processes

\* each process loops on the following steps:
\* r (polling to receive a message)
\* w1 (writes to the first database)
\* w2 (writes to the second database)
Step == {"r", "w1", "w2"}

\* one message chosen as default value
default == CHOOSE m \in Message: TRUE

VARIABLE db1
VARIABLE db2
\* the next step of each process
VARIABLE processNextStep
 \* the current message being processed by each process
VARIABLE processCurrentMessage

\* the tuple of all variables
vars == <<db1, db2, processNextStep, processCurrentMessage>>

TypeOK ==
    /\ db1 \in Message
    /\ db2 \in Message
        \* a function mapping processes to steps
    /\ processNextStep \in [Process -> Step]
        \* a function mapping processes to messages
    /\ processCurrentMessage \in [Process -> Message]

Init ==
    /\ db1 = default
    /\ db2 = default
    \* all processes start in the receiving state
    /\ processNextStep = [p \in Process |-> "r"]
    \* all processes start with the default message (but it will be discarded on the first receive step)
    /\ processCurrentMessage = [p \in Process |-> default]

\* some process receives some (non-default) message
\* its next step from 'r' becomes 'w1'
\* its current message becomes the received one
\* everything else is unchanged
Receive == \E m \in Message \ {default}, p \in Process:
    /\ processNextStep[p] = "r"

    \* additional condition to ensure eventual consistency:
    \* /\ \A x \in Process: processNextStep[x] = "r"

    /\ processNextStep' = [processNextStep EXCEPT ![p] = "w1"]
    /\ processCurrentMessage' = [processCurrentMessage EXCEPT ![p] = m]
    /\ UNCHANGED <<db1, db2>>

\* some process writes its current message to the first database
\* and advances its 'program counter' to 'w2'
Write1 == \E p \in Process:
    /\ processNextStep[p] = "w1"
    /\ processNextStep' = [processNextStep EXCEPT ![p] = "w2"]
    /\ db1' = processCurrentMessage[p]
    /\ UNCHANGED <<db2, processCurrentMessage>>

\* some process writes its current message to the second database
Write2 == \E p \in Process:
    /\ processNextStep[p] = "w2"
    /\ processNextStep' = [processNextStep EXCEPT ![p] = "r"]
    /\ db2' = processCurrentMessage[p]
    /\ UNCHANGED <<db1, processCurrentMessage>>

Next ==
    \/ Receive
    \/ Write1
    \/ Write2

Liveness == WF_vars(Write1 \/ Write2)

Spec == Init /\ [][Next]_vars /\ Liveness

\* this property is violated in models with at least two processes
\* (and two messages besides the default one)
DbConsistency == []<>(db2 = db1)
====
