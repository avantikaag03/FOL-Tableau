exception ParseError;

open AST
open TABLEAU

structure Asgn1LrVals = Asgn1LrValsFun(structure Token = LrParser.Token)
structure Asgn1Lex = Asgn1LexFun(structure Tokens = Asgn1LrVals.Tokens);
structure Asgn1Parser =
      Join(structure LrParser = LrParser
               structure ParserData = Asgn1LrVals.ParserData
               structure Lex = Asgn1Lex)
     
fun invoke lexstream =
        let
            fun error(value, pos, _) =
                let
                    val (l, c) = pos
                in
                    TextIO.output(TextIO.stdOut,"Parse Error:" ^ (Int.toString l) ^ ":" ^ (Int.toString c) ^ ":" ^ value ^ "\n")
                end
        in
            Asgn1Parser.parse(0, lexstream, error, ()) handle Asgn1Parser.ParseError => raise ParseError
        end

fun fileToLexer infilename =
    let val instream = TextIO.openIn infilename;
        val lexer = Asgn1Parser.makeLexer (fn _ => TextIO.input instream);
    in
        lexer
    end 
        
fun parse (lexer) =
    let
        val (result, lexer) = invoke lexer
        val (nextToken, lexer) = Asgn1Parser.Stream.get lexer
    in
        result
    end

val parseFile = parse o fileToLexer



fun flasl2ast(infilename) =
    let
        val argument = parseFile infilename
    in
        proptableau(argument)
    end


fun writeanswer(assignment, outname) =
    let
        val outstream = TextIO.openOut outname
        val (a, b) = assignment
        fun helper(nil) = TextIO.output(outstream, "") | helper(l) =
            let
                val hd::tl = l
                val (x, y) = hd
            in
                (if y then TextIO.output(outstream, x ^ " : True\n") else TextIO.output(outstream, x ^ " : False\n")); helper(tl)
            end
    in
        TextIO.output(outstream, a ^ "\n");
        helper(b);
        TextIO.closeOut outstream
    end



fun flasl2valid(infilename) =
    let
        val assignment = flasl2ast(infilename)
        val x = String.size(infilename)
        val name = String.substring(infilename, 0, x-6)
        val outname = String.concat([name, ".out"])
    in
        writeanswer(assignment, outname)
    end