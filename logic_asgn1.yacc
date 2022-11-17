(* User declarations *)

(* EBNF SPECIFICATION
program ::= argument .
argument ::= proplist "THEREFORE" prop PERIOD .
proplist ::= prop PERIOD proplist | epsilon .
argument ::= prop PERIOD argument | "THEREFORE" prop .
prop ::= "IF" prop "THEN" prop "ELSE" prop | conditional "IFF" prop | conditional .
conditional ::= "IF" union "THEN" conditional | conditional "IF" union | union | "IF" "IF" prop "THEN" prop "ELSE" prop "THEN" conditional .
union ::= union "OR" intersection | intersection | union "OR" "IF" prop "THEN" prop "ELSE" prop | union "OR" "IF" union "THEN" conditional .
intersection ::= intersection "AND" negation | negation | intersection "AND" "IF" prop "THEN" prop "ELSE" prop | intersection "AND" "IF" union "THEN" conditional .
negation ::= "NOT" negation | parenthesis | "NOT" "IF" prop "THEN" prop "ELSE" prop | "NOT" "IF" union "THEN" conditional .
parenthesis ::= LPAREN prop RPAREN | atom .
atom ::= atom WORD | WORD .
PERIOD ::= "." .
LPAREN ::= "(" .
RPAREN ::= ")" .
WORD ::= {uppercaseLetter}(no_upper{no_upper}{uppercaseLetter}){(no_upper{no_upper}{uppercaseLetter})} .
uppercaseLetter ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" .
no_upper ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" | "!" | "#" | "$" | "%" | "&" | "'" | "*" | "+" | "," | "-" | "/" | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" | ":" | ";" | "<" | "=" | ">" | "?" | "@" | "[" | "\" | "]" | "^" | "_" | "`" | "{" | "}" | "|" | "~" .
*)

%%
(* required declarations *)
%name Asgn1

%term WORD of string | NOT | AND | OR | IF | THEN | ELSE | IFF | THEREFORE | LPAREN | RPAREN | PERIOD | QUOTE | EOF

%nonterm program of AST.Argument | argument of AST.Argument | prop of AST.Prop | atom of string | proplist of AST.Prop list

%pos int * int


(* Optional declarations *)
%eop EOF
%noshift EOF

(* header *)

%right IFF
%left IF
%right THEN ELSE
%left OR
%left AND
%right NOT


%start program

%verbose

%%

program : argument (argument)

argument : proplist THEREFORE prop PERIOD (AST.HENCE(proplist, prop))

proplist : prop PERIOD proplist (prop :: proplist) | ([])

prop : IF prop THEN prop ELSE prop (AST.ITE(prop1, prop2, prop3)) | prop IFF prop (AST.BIC(prop1, prop2)) | IF prop THEN prop (AST.COND(prop1, prop2)) | prop IF prop (AST.COND(prop2, prop1)) | prop OR prop (AST.OR(prop1, prop2)) | prop AND prop (AST.AND(prop1, prop2)) | NOT prop (AST.NOT(prop)) | LPAREN prop RPAREN (prop) | QUOTE atom QUOTE (AST.ATOM(atom))

atom : atom WORD (atom ^ " " ^ WORD) | WORD (WORD)