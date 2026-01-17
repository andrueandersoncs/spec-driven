---
description: Extract formal assertions from natural language requirements
argument-hint: [focus-area]
allowed-tools: Read, Write, Edit, AskUserQuestion
model: sonnet
---

# Interview Engine

Run the interview loop to extract formal assertions from user requirements.

## Prerequisites

Check that `specs/assertions.json` exists. If not, instruct user to run `/probe-domain` first.

Load current state from `specs/assertions.json`.

## Focus Area

If $ARGUMENTS provided, focus interview on that area (e.g., "authentication", "payments", "error handling").

If no argument, continue from where previous interview left off or start with pending seed assertions.

## Interview Loop

### Step 1: Context Loading

Read current assertions from `specs/assertions.json`.
Identify:
- Pending assertions awaiting confirmation
- Confirmed assertions (for context)
- Gaps in coverage based on actor × capability matrix

### Step 2: Assertion Generation

Based on user input or current focus area, generate candidate assertions.

For each requirement mentioned by user:
1. Identify if it's structure (single moment) or behavior (sequences)
2. Generate 3-5 candidate assertions that capture the requirement
3. Classify each using the assertion-taxonomy skill

### Step 3: Present Assertions

Use AskUserQuestion to present assertion batch:

**Question**: "Please review these assertions. Select those that are correct as stated."

Present each assertion with:
- ID (e.g., A-001)
- Natural language statement
- Classification (Structure/Behavior)
- Proposed formal construct

**Options**: Each assertion as a selectable option, plus "None of these are correct"

Allow multi-select so user can confirm multiple at once.

### Step 4: Process Feedback

For confirmed assertions:
- Update status to "confirmed" in assertions.json
- Generate formal spec (Dafny or TLA+) based on classification

For assertions not selected:
- Ask follow-up: "Would you like to refine any of these, or provide your own alternative?"
- If user provides refinement, create new assertion with refined text
- If user denies, mark as "denied"

### Step 5: Parameterized Assertions

When assertions contain parameters, ask user to fill in values:

**Question**: "This assertion needs specific values:"
"Rate limit is <X> requests per <Y> time unit"

**Options**:
- X: (text input for number)
- Y: (options: second, minute, hour, day)

### Step 6: Decomposition

If user responds "it depends" to any assertion:
- Ask what it depends on
- Generate decomposed assertions covering each case
- Present decomposed assertions for confirmation

### Step 7: Implied Assertions

After confirming assertions, check for implications:
- Does A imply B?
- Are there standard patterns that follow from confirmed assertions?

Present implied assertions: "Based on what you've confirmed, these also seem true. Confirm?"

### Step 8: Loop Control

Continue interview until:
1. User signals "that's everything for this scope"
2. All pending assertions are processed
3. Actor × capability matrix is covered

## Formal Spec Generation

For each confirmed assertion, generate formal spec:

### Structure Assertions → Dafny

Write to `specs/dafny/structure.dfy`:
- Refinement types for data constraints
- Invariants for entity constraints
- Method contracts for operations

Use the dafny-patterns skill for correct syntax.

### Behavior Assertions → TLA+

Write to `specs/tla/behavior.tla`:
- State variables
- Initial state
- Actions for each operation
- Safety and liveness properties

Use the tla-patterns skill for correct syntax.

## Persistence

After each assertion batch:
1. Update `specs/assertions.json` with new/modified assertions
2. Write/update formal spec files
3. Save interview progress for resumption

## Output

Summarize interview progress:
- Assertions confirmed this session
- Assertions pending review
- Coverage of actor × capability matrix
- Formal specs generated/updated
- Next steps (more interview, or ready to /verify)
