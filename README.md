# `impc`
> An IMP compiler.

## Grammar
As an ANTLR4 grammar, IMP is specified as follows.
```
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

cmd  : 'skip'                                     #Skip
     | variable=VAR ':=' expression=aexp          #Assignment
     | first=cmd ';' second=cmd                   #Sequence
     | 'if' condition=bexp 'then' truecase=cmd 'else' falsecase=cmd 'fi'  #If
     | 'while' condition=bexp 'do' body=cmd 'od'  #While
     ;
     
VAR  : [a-zA-Z][a-zA-Z0-9_]* ;
INT  : [0-9]+ ;
WS   : [ \r\n\t] -> skip ;
```
