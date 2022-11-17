structure Tokens = Tokens

	type pos = int * int
	type svalue = Tokens.svalue
	type ('a, 'b) token = ('a, 'b) Tokens.token
	type lexresult = (svalue, pos) token

	val pos = ref((1, 0))
	val eof = fn () => (Tokens.EOF(!pos, !pos))
	exception ScanError

	val error = fn (value, pos, _) =>
		let
			val (l, c) = pos
		in
	 		TextIO.output(TextIO.stdOut, "Unknown Token:" ^ (Int.toString l) ^ ":" ^ (Int.toString (c) ^ ":" ^ value ^ "\n")); raise ScanError
	 	end

	fun lineinc(pos, inc) =
		let
			val (l, r) = pos
		in
			(l+inc, 1)
		end

	fun colinc(pos, inc) =
		let
			val (l, r) = pos
		in
			(l, r+inc)
		end


%%
%header (functor Asgn1LexFun(structure Tokens:Asgn1_TOKENS));

alpha = [A-Za-z];
ws = [\ ];
tabs = [\t];
num = [0-9];
caps = [A-Z];
not_caps =[\!\#-\'\*-\-\/-@\[-\~A-Z];
quote = [\"];
%%

"\""     => (pos := colinc(!pos, 1); Tokens.QUOTE(!pos, !pos));

\n       => (pos := lineinc(!pos, 1); lex());

\r\n       => (pos := lineinc(!pos, 1); lex());

{ws}+    => (pos := colinc(!pos, 1); lex());

{tabs}+  => (pos := colinc(!pos, 4); lex());

"NOT"	 => (pos := colinc(!pos, 3); Tokens.NOT(!pos, !pos));

"AND"	 => (pos := colinc(!pos, 3); Tokens.AND(!pos, !pos));

"OR"	 => (pos := colinc(!pos, 2); Tokens.OR(!pos, !pos));

"IF"	 => (pos := colinc(!pos, 2); Tokens.IF(!pos, !pos));

"THEN"	 => (pos := colinc(!pos, 4); Tokens.THEN(!pos, !pos));

"ELSE"	 => (pos := colinc(!pos, 4); Tokens.ELSE(!pos, !pos));

"IFF"    => (pos := colinc(!pos, 3); Tokens.IFF(!pos, !pos));

"THEREFORE" => (pos := colinc(!pos, 9); Tokens.THEREFORE(!pos, !pos));

"("		 => (pos := colinc(!pos, 1); Tokens.LPAREN(!pos, !pos));

")"		 => (pos := colinc(!pos, 1); Tokens.RPAREN(!pos, !pos));

"."      => (pos := colinc(!pos, 1); Tokens.PERIOD(!pos, !pos));

{not_caps}* => (pos := colinc(!pos, size(yytext)); Tokens.WORD(yytext, !pos, !pos));

.        => (pos := colinc(!pos, 1); error (yytext, !pos, !pos); lex());