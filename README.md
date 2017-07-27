# CS350A Homework 3 [Interpreter with threads]

### Structure
- Main.oz : Interpreter for AST
- SemanticStack.oz : A multistack (using cell) with push and pop function
- ProcessRecords.oz : Processing of records (code provided)
- SingleAssignmentStore.oz : SAS implementation using dictionary
- Unify.oz : Code for unification algorithm (code provided)

### Build and Run
Standalone compilation using ozc compiler
```
ozc -c Main.oz -o Main
```
```
ozengine Main
```
With oz-sublime plugin, use Ctrl+B/Ctrl+Shift+B on Main.oz

### Short Description
We have used cells to simulate a stack of pair of statement and environment (file: SemanticStack.oz). In this cell, we are keeping a list initialized with nil. To simulate as a stack, we have added Push procedure and Pop function. In push procedure, we prepend the element (which is a pair of statment and environment) in the list. Pop extracts the top element and evaluates to this value. Threads are supported as well

Execution (Interpretion) is carried out by a recursive procedure which pops from the semantic stack, and executes the statements as described in comments in Main.oz

### Authors
*[Anurag Misra](https://github.com/MishRanu)