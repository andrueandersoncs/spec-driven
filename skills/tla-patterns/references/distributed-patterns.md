# Distributed Systems Patterns in TLA+

Comprehensive patterns for modeling distributed systems in TLA+. These patterns are commonly used in real-world distributed systems.

> **Source**: [TLA+ Examples Repository](https://github.com/tlaplus/Examples) - Contains complete, verified implementations of these and many more specifications.

## Two-Phase Commit

The two-phase commit protocol ensures all participants in a distributed transaction either commit or abort together.

> **Reference**: See `specifications/TwoPhase` in the [TLA+ Examples](https://github.com/tlaplus/Examples) for the complete specification.

### Pattern: Basic Two-Phase Commit

```tla
---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS ResourceManagers   \* Set of participating nodes

VARIABLES
  rmState,     \* Resource manager states
  tmState,     \* Transaction manager state
  tmPrepared,  \* Set of RMs that have prepared
  msgs         \* Messages in transit

\* Natural language: "All participants agree to commit or all abort"

TypeOK ==
  /\ rmState \in [ResourceManagers -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq ResourceManagers
  /\ msgs \subseteq [type: {"Prepared", "Commit", "Abort"}, rm: ResourceManagers]

Init ==
  /\ rmState = [rm \in ResourceManagers |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

\* RM prepares (votes yes)
RMPrepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

\* RM chooses to abort (votes no)
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* TM receives prepare message
TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \union {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

\* TM decides to commit (all prepared)
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = ResourceManagers
  /\ tmState' = "committed"
  /\ msgs' = msgs \union {[type |-> "Commit", rm |-> rm] : rm \in ResourceManagers}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* TM decides to abort
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \union {[type |-> "Abort", rm |-> rm] : rm \in ResourceManagers}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* RM receives commit
RMRcvCommit(rm) ==
  /\ [type |-> "Commit", rm |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM receives abort
RMRcvAbort(rm) ==
  /\ [type |-> "Abort", rm |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
  \/ \E rm \in ResourceManagers:
       \/ RMPrepare(rm)
       \/ RMChooseToAbort(rm)
       \/ TMRcvPrepared(rm)
       \/ RMRcvCommit(rm)
       \/ RMRcvAbort(rm)
  \/ TMCommit
  \/ TMAbort

\* Safety: Never both committed and aborted
Consistency ==
  ~(\E rm1, rm2 \in ResourceManagers:
      rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

\* Safety: TM commits only if all prepared
TMCommitConsistency ==
  tmState = "committed" => tmPrepared = ResourceManagers

Spec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>

=============================================================================
```

### TLC Configuration for Two-Phase Commit

```
SPECIFICATION Spec
CONSTANTS
    ResourceManagers = {rm1, rm2, rm3}
INVARIANT TypeOK
INVARIANT Consistency
INVARIANT TMCommitConsistency
```

---

## Leader Election

Leader election ensures exactly one node acts as leader at any time. Critical for consensus protocols.

> **Reference**: See `specifications/Paxos` and `specifications/Raft` in the [TLA+ Examples](https://github.com/tlaplus/Examples) for production-grade leader election specifications.

### Pattern: Simple Leader Election

```tla
---------------------------- MODULE LeaderElection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes

VARIABLES
  leader,  \* Current leader (None if no leader)
  term     \* Election term (monotonically increasing)

None == CHOOSE n : n \notin Nodes

\* Natural language: "Exactly one leader at any time"

TypeOK ==
  /\ leader \in Nodes \union {None}
  /\ term \in Nat

Init ==
  /\ leader = None
  /\ term = 0

\* A node becomes leader
BecomeLeader(n) ==
  /\ leader = None
  /\ leader' = n
  /\ term' = term + 1

\* Leader steps down (timeout, partition, etc.)
StepDown ==
  /\ leader # None
  /\ leader' = None
  /\ UNCHANGED term

Next ==
  \/ \E n \in Nodes: BecomeLeader(n)
  \/ StepDown

\* Safety: At most one leader per term
OneLeaderPerTerm ==
  \A n1, n2 \in Nodes:
    (leader = n1 /\ leader = n2) => n1 = n2

\* Liveness: Eventually a leader is elected (requires fairness)
EventuallyLeader == <>(leader # None)

Fairness == WF_<<leader, term>>(Next)

Spec == Init /\ [][Next]_<<leader, term>> /\ Fairness

=============================================================================
```

---

## Termination Detection (Ring-Based)

Detect when all processes in a distributed system have become idle. Based on Dijkstra's EWD840 algorithm.

> **Reference**: See `specifications/ewd840` in the [TLA+ Examples](https://github.com/tlaplus/Examples) for Dijkstra's original termination detection algorithm.

### Pattern: Termination Detection (EWD840)

```tla
---------------------------- MODULE TerminationDetection ----------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes  \* Ordered ring of nodes

VARIABLES
  active,   \* Which nodes are active
  color,    \* Node colors (white = clean, black = sent message to lower node)
  token     \* Token position and color

\* Natural language: "Detect when all processes are idle"

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> {"white", "black"}]
  /\ token \in [pos: Nodes, color: {"white", "black"}]

\* Initial state: all active, all white, token at node 0
Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ color = [n \in Nodes |-> "white"]
  /\ token = [pos |-> 0, color |-> "white"]

\* A node becomes inactive
BecomeInactive(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<color, token>>

\* A node sends a message (can activate other nodes)
SendMessage(sender, receiver) ==
  /\ active[sender]
  /\ active' = [active EXCEPT ![receiver] = TRUE]
  \* If sending to lower-numbered node, sender turns black
  /\ IF receiver < sender
     THEN color' = [color EXCEPT ![sender] = "black"]
     ELSE UNCHANGED color
  /\ UNCHANGED token

\* Pass token around the ring
PassToken(n) ==
  /\ token.pos = n
  /\ ~active[n]
  /\ LET nextNode == (n + 1) % Cardinality(Nodes)
         newColor == IF color[n] = "black" THEN "black" ELSE token.color
     IN token' = [pos |-> nextNode, color |-> newColor]
  /\ color' = [color EXCEPT ![n] = "white"]  \* Reset color after passing
  /\ UNCHANGED active

\* Termination is detected when token returns to node 0 white
\* and node 0 is inactive and white
TerminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ ~active[0]
  /\ color[0] = "white"

Next ==
  \/ \E n \in Nodes: BecomeInactive(n)
  \/ \E s, r \in Nodes: s # r /\ SendMessage(s, r)
  \/ \E n \in Nodes: PassToken(n)

\* Safety: Only declare termination when all truly idle
TerminationSafe ==
  TerminationDetected => \A n \in Nodes: ~active[n]

Spec == Init /\ [][Next]_<<active, color, token>>

=============================================================================
```

---

## Message Passing Patterns

### Reliable Delivery

```tla
\* Messages can be lost but not corrupted
\* Sender retries until acknowledgment received
VARIABLES msgs, acked

SendWithRetry(m) ==
  /\ msgs' = msgs \union {m}
  /\ UNCHANGED acked

Receive(m) ==
  /\ m \in msgs
  /\ ProcessMessage(m)
  /\ acked' = acked \union {m.id}

\* Lossy channel: messages can disappear
LoseMessage(m) ==
  /\ m \in msgs
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED acked
```

### FIFO Channels

```tla
\* Channels preserve message order
VARIABLES channels  \* [sender, receiver] -> Seq(Message)

SendFIFO(s, r, m) ==
  channels' = [channels EXCEPT ![<<s, r>>] = Append(@, m)]

ReceiveFIFO(s, r) ==
  /\ Len(channels[<<s, r>>]) > 0
  /\ LET m == Head(channels[<<s, r>>])
     IN /\ ProcessMessage(m)
        /\ channels' = [channels EXCEPT ![<<s, r>>] = Tail(@)]
```

---

## External References

- [TLA+ Examples Repository](https://github.com/tlaplus/Examples) - 100+ verified specifications
- [TwoPhase Commit Spec](https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase)
- [Paxos Spec](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos)
- [Raft Spec](https://github.com/tlaplus/Examples/tree/master/specifications/Raft)
- [EWD840 Termination Detection](https://github.com/tlaplus/Examples/tree/master/specifications/ewd840)
