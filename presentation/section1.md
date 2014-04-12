Problem description
===================

Context
-------

### Source code, Stack code, eval, compile, exec

  * The type of the interpreter states type preservation


Compiler correctness
--------------------

### What does "correct" mean?

  * Commutative diagram?


Extending the source language
-----------------------------

### Extension

  * Sequencing expressions
  * Enables "branching", but with _shared suffix_


### Code duplication

  * The "normal" _compile_ function will duplicate the common suffix
  * Having Bytecode defined as _graph_ (structured graph) instead of tree
    would solve this problem
      + But proofs would be harder


### Graph and tree representations are equivalent

  * Equations
  * Make Bytecode a functor (BytecodeF)
      + Two type-level fixpoint operators give two different Bytecode versions:
          - HTree gives us BytecodeT
          - HGraph gives us BytecodeG

  * Now for the implementation

