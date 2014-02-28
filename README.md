infomtpt-verified-compilers
===========================

Final project of the master's course "Theory of Programming and Types" at Utrecht University (winter 2014)

### References

["A type-correct, stack-safe, provably correct expression compiler in Epigram" - James McKinna, Joel Wright][1]
["Proving Correctness of Compilers using Structured Graphs" - Patrick Bahr][2]

[1]: <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.105.4086>
[2]: <http://www.diku.dk/~paba/pubs/files/bahr14esop-preprint.pdf>

### Goal(s)

Use a dependently-typed programming language (Agda) to define:

  * A simple computation language (`Src`)
      + With an associated evaluation semantics (`eval`)

  * A stack-based intermediate code (`Bytecode`)
      + Operating over stacks of values (`Stack`)
      + With an associated execution semantics (`exec`)

  * A **compiler** (`compile`) performing _source-to-machine code transformation_

In the dependently-typed setting, prove compiler correctness, i.e,
_evaluating_ a source expression directly must result in the same value
as the value left at the top of the stack after _executing the compiled bytecode_.

Some properties that might be proven along the way:

  * **Type preservation:** Having an isomorphism between _object-language types_ and _host-language types_,
    the evaluation semantics preserves the types of expressions upto this isomorphism

  * **Stack safety:** The execution of any sequence of bytecode instructions will never get _stuck_
    due to the stack having fewer values then required
      + Neither will values on top of the stack ever be of a type different than required by the instruction

