# TLC Model Checker Guide

> **Source**: This reference consolidates information from the [TLA+ Repository](https://github.com/tlaplus/tlaplus), [TLA+ Wiki](https://docs.tlapl.us/using:tlc:start), and [Learn TLA+](https://learntla.com/).

## Overview

TLC is an explicit-state model checker for TLA+ specifications. It systematically explores all reachable states to verify invariants and temporal properties.

**Requirements**: Java Runtime Environment version 11 or later.

## Installation

### Download Release

Download the latest release from: https://github.com/tlaplus/tlaplus/releases/

### Build from Source

```bash
# Requirements: JDK 11 and ant
cd tlaplus/tlatools/org.lamport.tlatools
ant -f customBuild.xml compile dist
# Output: dist/tla2tools.jar
```

## Running TLC

### Basic Invocation

```bash
java -jar tla2tools.jar MySpec.tla
```

TLC automatically searches for `MySpec.cfg` in the same directory.

### Performance Optimization

For optimal throughput, use the parallel garbage collector:

```bash
java -XX:+UseParallelGC -jar tla2tools.jar MySpec.tla
```

> **Note**: This setting improves both simulation and model-checking performance compared to G1GC.

## Essential Command-Line Options

| Option | Description |
|--------|-------------|
| `-config file` | Specify configuration file (defaults to SPEC.cfg) |
| `-workers num` | Set worker threads; use `auto` for automatic |
| `-simulate` | Run in simulation mode |
| `-depth num` | Set simulation depth (default: 100) |
| `-coverage min` | Collect coverage metrics at intervals |
| `-checkpoint min` | Set checkpoint intervals (default: 30) |
| `-deadlock` | Disable deadlock checking |
| `-continue` | Keep running after invariant violations |
| `-dumpTrace format file` | Export error traces (`tla` or `json`) |
| `-view` | Apply VIEW when displaying states |
| `-difftrace` | Show only differences between successive states |

### Example Commands

```bash
# Use 4 worker threads
java -jar tla2tools.jar -workers 4 MySpec.tla

# Run simulation mode
java -jar tla2tools.jar -simulate -depth 1000 MySpec.tla

# Dump error trace as JSON
java -jar tla2tools.jar -dumpTrace json errors.json MySpec.tla

# Continue after first violation (find multiple bugs)
java -jar tla2tools.jar -continue MySpec.tla

# Get help
java -jar tla2tools.jar -help
```

## Interpreting TLC Results

### Success Output

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states...
  1234567 states generated, 123456 distinct states found, 0 states left on queue.
```

### Error Types

| Error | Meaning | Action |
|-------|---------|--------|
| **Invariant violated** | Safety property fails in some reachable state | Fix spec or weaken invariant |
| **Temporal property violated** | Liveness property fails | Add fairness or fix spec |
| **Deadlock reached** | No enabled actions from some state | Add actions or fix guards |
| **State space too large** | Model too big to check exhaustively | Add constraints or symmetry |

## Understanding Invariant Violations

> An invariant is a condition that "must be true on every single step of the program, regardless of the initial values, regardless of where we are."
>
> *Source: [Learn TLA+ - Invariants](https://learntla.com/core/invariants.html)*

### Type Invariants

The foundational approach validates that variables belong to specific sets:

```tla
TypeInvariant ==
  /\ balance \in Int
  /\ state \in {"idle", "working", "done"}
  /\ items \subseteq AllItems
```

### Conditional Invariants

Use implication (`=>`) to restrict when invariants apply:

```tla
\* Only check correctness when algorithm finishes
IsCorrect == pc = "Done" => result = ExpectedResult
```

### Common Invariant Mistakes

**Critical mistake**: Using `=>` with existential quantifiers (`\E`).

```tla
\* WRONG: becomes true when precondition is false
Wrong == \E x \in S: SomeCondition(x) => SomeProperty(x)

\* CORRECT: use /\ instead of => with \E
Correct == \E x \in S: SomeCondition(x) /\ SomeProperty(x)
```

> The expression with `=>` becomes true when the precondition is false, regardless of the consequent. Use `/\` (AND) instead for existential quantifiers.
>
> *Source: [Learn TLA+](https://learntla.com/core/invariants.html)*

## Understanding Error Traces

When TLC detects a violation, it displays a step-by-step trace:

1. **Initial state**: Starting variable values
2. **Action sequence**: Each action and resulting state
3. **Violation point**: State where invariant/property fails

### Reading Traces

The `pc` variable (program counter) tracks current labels. Use it to understand control flow:

```tla
\* Check post-execution conditions
PostCondition == pc = "Done" => balance >= 0
```

### Diff Traces

Use `-difftrace` to show only changed variables between states (helpful for complex specs).

## Liveness Checking

### Fairness Requirements

Liveness properties require fairness assumptions to be meaningful:

```tla
\* Weak Fairness: if action is continuously enabled, it eventually happens
Spec == Init /\ [][Next]_vars /\ WF_vars(SomeAction)

\* Strong Fairness: if action is repeatedly enabled, it eventually happens
Spec == Init /\ [][Next]_vars /\ SF_vars(SomeAction)
```

### Liveness Check Timing

Control when liveness is checked with `-lncheck`:

| Mode | Behavior |
|------|----------|
| `default` | Check during state exploration |
| `final` | Check only after state graph complete |
| `seqfinal` | Sequential final check (use for large models) |

```bash
java -jar tla2tools.jar -lncheck final MySpec.tla
```

## Debugging Techniques

### Debug Mode

```bash
java -jar tla2tools.jar -debugger nosuspend MySpec.tla
```

Integrates with the TLA+ VSCode extension for:
- Temporary halting during exploration
- Variable inspection
- Step-by-step execution

### State Space Issues

For small models, use single-worker mode for consistent depth reporting:

```bash
java -jar tla2tools.jar -workers 1 MySpec.tla
```

### Generate State Graph

```bash
java -jar tla2tools.jar -dump dot states.dot MySpec.tla
```

Produces a GraphViz DOT file for visualization.

## Configuration File (.cfg)

### Basic Structure

```
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT SafetyProperty
PROPERTY LivenessProperty
```

### Constants

```
CONSTANT
    MaxBalance = 1000
    Processes = {p1, p2, p3}
```

### State Constraints

Limit state space for tractable checking:

```
CONSTRAINT
    balance <= 10000
    Len(history) <= 20
```

### Symmetry Sets

Reduce state space when elements are interchangeable:

```
SYMMETRY Symmetry
```

Where `Symmetry` is defined in the spec as a permutation set.

## Troubleshooting

### "SpecTE Generation Issues"

When using `-generateSpecTE`:
- Add `nomonolith` option to avoid duplicate operator warnings
- Rename model values to start with non-numeric characters if CONSTANT errors occur

### "State Space Explosion"

1. Add tighter state constraints
2. Use symmetry reduction
3. Reduce constant values (e.g., smaller `MaxBalance`)
4. Consider simulation mode for large models

### "Timeout During Liveness Check"

Liveness checking can be expensive. Try:
1. Use `-lncheck final` to check only after exploration
2. Simplify temporal properties
3. Use stronger fairness assumptions

## External References

- [TLA+ Repository](https://github.com/tlaplus/tlaplus) - Official tools
- [TLA+ Wiki](https://docs.tlapl.us/) - Community documentation
- [TLA+ Examples](https://github.com/tlaplus/Examples) - Curated specifications
- [Learn TLA+](https://learntla.com/) - Interactive tutorial
- [TLA+ Cheatsheet (PDF)](https://lamport.azurewebsites.net/tla/summary-standalone.pdf) - Quick reference
- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html) - Official website with video course
