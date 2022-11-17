structure FOL =
struct
datatype term = VAR of string
| FUN of string * term list
| CONST of string (* for generated constants only *)
datatype Pred = FF (* special constant for closing a tableau path *)
| ATOM of string * term list
| NOT of Pred
| AND of Pred * Pred
| OR of Pred * Pred
| COND of Pred * Pred
| BIC of Pred * Pred
| ITE of Pred * Pred * Pred
| ALL of term * Pred
| EX of term * Pred
datatype Argument = HENCE of Pred list * Pred
datatype tree = EMPTY of Pred | UNTREE of Pred * tree | BINTREE of Pred * tree * tree
(*val mktableau: Pred list * Pred -> unit*) (* outputs file "tableau.dot" in dot format *)
(*val maketableau: Pred list * Pred -> Pred list*)
exception NotVAR (* Binding term in a quantified formula is not a variable *)
exception NotWFT (* term is not well-formed *)
exception NotWFP (* predicate is not well-formed *)
exception NotWFA (* argument is not well-formed *)
exception NotClosed (* a formula is not closed *)
end;