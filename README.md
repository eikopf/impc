# `impc`
> A compiler for the IMP programming language.
Currently, `impc run <program>` will parse the given program and invoke a valid tree-walk interpreter; in this condition it is ready to use for the relatively simple task of executing IMP programs. The development focus has shifted to implementing a minimal optimising backend targeting LLVM, which should supersede the interpreter when feature-complete.

## Installation and Usage
Assuming you have a Rust toolchain installed on your system (if not, follow [these instructions](https://rustup.rs)), then `impc` can be installed using `cargo install`.

```sh
# from crates.io
cargo install impc

# from source
cargo install --git https://github.com/eikopf/impc.git
```

With `impc` installed, run `impc --help` and `impc run --help` for the specific details of its usage. To run an IMP program, you can use the `impc run <filename>` command and optionally provide explicit bindings with the `--let` option if you want to avoid the interactive prompt stage.

## IMP
IMP is, largely speaking, a _deeply_ uninteresting language; its entire grammar can be given in a single 30-line ANTLR4 `.g4` file (see below), and its semantics are incredibly simple.

In IMP,
1. all variables are always in scope, and must have bound values prior to execution;
2. arithmetic expressions are evaluated with unsigned integer semantics, with the exception that subtraction saturates at 0;
3. arithmetic expressions are always defined, so integer overflow is undefined behaviour;
4. because integer overflow is UB and integers have no specified bitwidth, a strictly correct implementation should use arbitrary precision integers unless it can show that overflow cannot occur for some fixed-width type;
5. boolean expressions have the ordinary boolean semantics;
6. both boolean and arithmetic expressions do not define an order of evaluation, since they cannot produce side-effects;
7. commands are executed in-order, and only assignment commands can yield side-effects (namely value-binding);
8. `while` and `if` commands behave with the expected semantics.

These properties admit the single interesting characteristic of IMP: it is can be aggressively optimised. In general, commands can be arbitrarily reordered so long as the order of assignment commands is preserved, and even then it can often be shown that arbitrary reorderings of assignment commands are valid (i.e. if they are disjoint). In more complex situations, these properties can be used to unroll, inline, or almost entirely erase `while` and `if` commands.

```antlr
grammar IMP;

aexp : INT                                        #Atom
     | VAR                                        #Variable
     | '(' inner=aexp ')'                         #Brackets
     | left=aexp '*' right=aexp                   #Mult
     | left=aexp '+' right=aexp                   #Add
     | left=aexp '-' right=aexp                   #Sub
     ;

bexp : 'true'                                     #True
     | 'false'                                    #False
     | left=aexp '=' right=aexp                   #Equal
     | left=aexp '<' right=aexp                   #Smaller
     | left=aexp '>' right=aexp                   #Greater
     | left=aexp '<>' right=aexp                  #Inequality
     | 'not' inner=bexp                           #Not
     | '(' left=bexp 'and' right=bexp ')'         #And
     | '(' left=bexp 'or' right=bexp ')'          #Or
     ;

cmd  : 'skip'                                                               #Skip
     | variable=VAR ':=' expression=aexp                                    #Assignment
     | first=cmd ';' second=cmd                                             #Sequence
     | 'if' condition=bexp 'then' truecase=cmd 'else' falsecase=cmd 'fi'    #If
     | 'while' condition=bexp 'do' body=cmd 'od'                            #While
     ;
     
VAR  : [a-zA-Z][a-zA-Z0-9_]* ;
INT  : [0-9]+ ;
WS   : [ \r\n\t] -> skip ;
```
