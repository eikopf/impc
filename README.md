# `impc`
> A compiler for the IMP programming language.

## IMP
IMP is, largely speaking, a _deeply_ uninteresting language. Its entire grammar can be given in a single 30-line ANTLR4 `.g4` file (see below), and its semantics are incredibly simple.

In IMP,
1. all variables are always in scope, and must have bound values prior to execution;
2. arithmetic expressions are evaluated with unsigned integer semantics, with the exception that subtraction saturates at 0;
3. arithmetic expressions are always defined, so integer overflow is undefined behaviour;
4. because integer overflow is UB and integers have no specified bitwidth, a strictly correct implementation should use arbitrary precision integers unless it can show that overflow cannot occur for some fixed-width type;
5. boolean expressions have the ordinary boolean semantics;
6. both boolean and arithmetic expressions do not define an order of evaluation, since they cannot produce side-effects;
7. commands are executed in-order, and only assignment commands can yield side-effects (namely value-binding);
8. `while` and `if` commands behave with the expected semantics.

These properties admit the single interesting characteristic of IMP: it is can be aggressively optimised. In general, commands can be arbitrarily reordered so long as the order of assignment commands is preserved, and even then it can often be shown that arbitrary reorderings of assignment commands are valid (i.e. they are disjoint). In more complex situations, these properties can be used to unroll, inline, or almost entirely erase `while` and `if` commands.

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
