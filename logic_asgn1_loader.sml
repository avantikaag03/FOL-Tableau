CM.make("$/basis.cm");
CM.make("$/ml-yacc-lib.cm");
use "logic_asgn1_ast.sml";
use "logic_asgn1.yacc.sig";
use "logic_asgn1.yacc.sml";
use "logic_asgn1.lex.sml";
use "proptableau.sml";
use "logic_asgn1_load.sml";
Control.Print.printLength := 1000; (* set printing parameters so that *)
Control.Print.printDepth := 1000; (* we’ll see all details *)
Control.Print.stringDepth := 1000; (* and strings *)