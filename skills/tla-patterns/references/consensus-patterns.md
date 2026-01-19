# Consensus Patterns in TLA+

Patterns for modeling consensus algorithms and agreement protocols in TLA+.

> **Source**: [TLA+ Examples Repository](https://github.com/tlaplus/Examples) - Contains complete Paxos, Raft, and other consensus specifications.

## Quorum Systems

Quorums are the foundation of consensus: any two quorums must intersect, ensuring agreement.

### Pattern: Quorum Agreement

```tla
---------------------------- MODULE QuorumAgreement ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
  Nodes,    \* Set of participating nodes
  Quorums,  \* Set of quorums (subsets of Nodes)
  Values    \* Set of possible values

\* Quorum assumption: any two quorums intersect
ASSUME QuorumAssumption ==
  /\ \A Q \in Quorums: Q \subseteq Nodes
  /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}

VARIABLES votes  \* votes[n] = value node n voted for (or None)

None == CHOOSE v : v \notin Values

\* Natural language: "Decisions require majority agreement"

TypeOK ==
  votes \in [Nodes -> Values \union {None}]

Init ==
  votes = [n \in Nodes |-> None]

\* A node votes for a value
Vote(n, v) ==
  /\ votes[n] = None
  /\ votes' = [votes EXCEPT ![n] = v]

\* A value is chosen if a quorum votes for it
Chosen(v) ==
  \E Q \in Quorums: \A n \in Q: votes[n] = v

Next ==
  \E n \in Nodes, v \in Values: Vote(n, v)

\* Safety: At most one value chosen
Agreement ==
  \A v1, v2 \in Values:
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

Spec == Init /\ [][Next]_votes

=============================================================================
```

### TLC Configuration for Quorum

```
SPECIFICATION Spec
CONSTANTS
    Nodes = {n1, n2, n3, n4, n5}
    \* Majority quorums for 5 nodes
    Quorums = {{n1, n2, n3}, {n1, n2, n4}, {n1, n2, n5},
               {n1, n3, n4}, {n1, n3, n5}, {n1, n4, n5},
               {n2, n3, n4}, {n2, n3, n5}, {n2, n4, n5},
               {n3, n4, n5}}
    Values = {v1, v2}
INVARIANT TypeOK
INVARIANT Agreement
```

---

## Paxos (Simplified)

Paxos is the foundational consensus algorithm. This is a simplified single-decree version.

> **Reference**: See `specifications/Paxos` in [TLA+ Examples](https://github.com/tlaplus/Examples) for the complete multi-Paxos specification by Lamport.

### Pattern: Single-Decree Paxos

```tla
---------------------------- MODULE SimplePaxos --------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
  Acceptors,  \* Set of acceptor nodes
  Proposers,  \* Set of proposer nodes
  Quorums,    \* Set of quorums
  Values      \* Set of proposable values

ASSUME QuorumAssumption ==
  /\ \A Q \in Quorums: Q \subseteq Acceptors
  /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}

VARIABLES
  maxBal,     \* maxBal[a] = highest ballot acceptor a has seen
  maxVBal,    \* maxVBal[a] = ballot of highest vote by a
  maxVal,     \* maxVal[a] = value of highest vote by a
  msgs        \* Set of messages sent

None == CHOOSE v : v \notin Values

\* Natural language: "Proposer must get promises before proposing"

Message ==
  [type: {"1a"}, bal: Nat]
  \union
  [type: {"1b"}, acc: Acceptors, bal: Nat, mbal: Nat \union {-1}, mval: Values \union {None}]
  \union
  [type: {"2a"}, bal: Nat, val: Values]
  \union
  [type: {"2b"}, acc: Acceptors, bal: Nat, val: Values]

TypeOK ==
  /\ maxBal \in [Acceptors -> Nat \union {-1}]
  /\ maxVBal \in [Acceptors -> Nat \union {-1}]
  /\ maxVal \in [Acceptors -> Values \union {None}]
  /\ msgs \subseteq Message

Init ==
  /\ maxBal = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal = [a \in Acceptors |-> None]
  /\ msgs = {}

\* Phase 1a: Proposer sends prepare
Phase1a(b) ==
  /\ msgs' = msgs \union {[type |-> "1a", bal |-> b]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 1b: Acceptor responds to prepare (promise)
Phase1b(a) ==
  \E m \in msgs:
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ msgs' = msgs \union {[type |-> "1b", acc |-> a, bal |-> m.bal,
                             mbal |-> maxVBal[a], mval |-> maxVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVal>>

\* Phase 2a: Proposer sends accept (with value)
Phase2a(b, v) ==
  /\ ~\E m \in msgs: m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums:
       /\ \A a \in Q: \E m \in msgs: m.type = "1b" /\ m.acc = a /\ m.bal = b
       /\ \/ \A a \in Q:
              \E m \in msgs: m.type = "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = -1
          \/ \E c \in 0..b-1:
              /\ \E a \in Q, m \in msgs:
                   m.type = "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = c
              /\ \A a \in Q, m \in msgs:
                   m.type = "1b" /\ m.acc = a /\ m.bal = b => m.mbal =< c
              /\ \E a \in Q, m \in msgs:
                   m.type = "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = c /\ m.mval = v
  /\ msgs' = msgs \union {[type |-> "2a", bal |-> b, val |-> v]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 2b: Acceptor accepts value
Phase2b(a) ==
  \E m \in msgs:
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ msgs' = msgs \union {[type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val]}

Next ==
  \/ \E b \in Nat: Phase1a(b)
  \/ \E a \in Acceptors: Phase1b(a)
  \/ \E b \in Nat, v \in Values: Phase2a(b, v)
  \/ \E a \in Acceptors: Phase2b(a)

\* A value is chosen when accepted by a quorum
Chosen(v) ==
  \E b \in Nat, Q \in Quorums:
    \A a \in Q: \E m \in msgs: m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

\* Safety: At most one value chosen
Consistency ==
  \A v1, v2 \in Values: (Chosen(v1) /\ Chosen(v2)) => v1 = v2

Spec == Init /\ [][Next]_<<maxBal, maxVBal, maxVal, msgs>>

=============================================================================
```

---

## Raft Leader-Based Consensus

Raft uses a strong leader for simpler reasoning than Paxos.

> **Reference**: See `specifications/Raft` in [TLA+ Examples](https://github.com/tlaplus/Examples) for the complete Raft specification.

### Pattern: Raft Leader Election (Simplified)

```tla
---------------------------- MODULE RaftLeaderElection -------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Servers

VARIABLES
  currentTerm,  \* currentTerm[s] = server s's current term
  state,        \* state[s] = Follower | Candidate | Leader
  votedFor,     \* votedFor[s] = server that s voted for in current term (or None)
  votesGranted  \* votesGranted[s] = set of servers that voted for s

None == CHOOSE s : s \notin Servers

TypeOK ==
  /\ currentTerm \in [Servers -> Nat]
  /\ state \in [Servers -> {"Follower", "Candidate", "Leader"}]
  /\ votedFor \in [Servers -> Servers \union {None}]
  /\ votesGranted \in [Servers -> SUBSET Servers]

Init ==
  /\ currentTerm = [s \in Servers |-> 0]
  /\ state = [s \in Servers |-> "Follower"]
  /\ votedFor = [s \in Servers |-> None]
  /\ votesGranted = [s \in Servers |-> {}]

\* Server s times out and starts election
Timeout(s) ==
  /\ state[s] \in {"Follower", "Candidate"}
  /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
  /\ state' = [state EXCEPT ![s] = "Candidate"]
  /\ votedFor' = [votedFor EXCEPT ![s] = s]  \* Vote for self
  /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]

\* Server s grants vote to candidate c
RequestVote(s, c) ==
  /\ state[c] = "Candidate"
  /\ currentTerm[c] >= currentTerm[s]
  /\ votedFor[s] \in {None, c}
  /\ votedFor' = [votedFor EXCEPT ![s] = c]
  /\ votesGranted' = [votesGranted EXCEPT ![c] = @ \union {s}]
  /\ UNCHANGED <<currentTerm, state>>

\* Candidate s becomes leader
BecomeLeader(s) ==
  /\ state[s] = "Candidate"
  /\ Cardinality(votesGranted[s]) * 2 > Cardinality(Servers)  \* Majority
  /\ state' = [state EXCEPT ![s] = "Leader"]
  /\ UNCHANGED <<currentTerm, votedFor, votesGranted>>

\* Server s steps down (discovers higher term)
StepDown(s, t) ==
  /\ t > currentTerm[s]
  /\ currentTerm' = [currentTerm EXCEPT ![s] = t]
  /\ state' = [state EXCEPT ![s] = "Follower"]
  /\ votedFor' = [votedFor EXCEPT ![s] = None]
  /\ UNCHANGED votesGranted

Next ==
  \/ \E s \in Servers: Timeout(s)
  \/ \E s, c \in Servers: RequestVote(s, c)
  \/ \E s \in Servers: BecomeLeader(s)
  \/ \E s \in Servers, t \in Nat: StepDown(s, t)

\* Safety: At most one leader per term
ElectionSafety ==
  \A s1, s2 \in Servers:
    (state[s1] = "Leader" /\ state[s2] = "Leader" /\ currentTerm[s1] = currentTerm[s2])
    => s1 = s2

Spec == Init /\ [][Next]_<<currentTerm, state, votedFor, votesGranted>>

=============================================================================
```

---

## Consensus Properties Reference

### Safety Properties

| Property | Description | TLA+ Pattern |
|----------|-------------|--------------|
| Agreement | All nodes decide same value | `Chosen(v1) /\ Chosen(v2) => v1 = v2` |
| Validity | Decided value was proposed | `Chosen(v) => v \in ProposedValues` |
| Integrity | Each node decides at most once | `decided[n] # None => decided[n] = decided'[n]` |

### Liveness Properties (require fairness)

| Property | Description | TLA+ Pattern |
|----------|-------------|--------------|
| Termination | All correct nodes eventually decide | `<>(\A n \in Correct: decided[n] # None)` |
| Progress | If value proposed, eventually chosen | `Proposed(v) ~> Chosen(v)` |

---

## External References

- [TLA+ Examples: Paxos](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos)
- [TLA+ Examples: Raft](https://github.com/tlaplus/Examples/tree/master/specifications/Raft)
- [Paxos Made Simple (Lamport)](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)
- [In Search of an Understandable Consensus Algorithm (Raft paper)](https://raft.github.io/raft.pdf)
- [Learn TLA+ - Consensus](https://learntla.com/topics/consensus/)
