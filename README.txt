I have used my own code from assignment 1 for lexer and parser.
I have made some changes to the "logic_asgn1_load.sml" file, to integrate my file proptableau.sml with the files for assignment 1. This change includes a function for parsing the input, feeding it to proptableau.sml, and creating an output file with the result.


I have not explicitly created a makefile, since that can't be done in Windows. However, running my code is easy:
1. ml-lex logic_asgn1.lex
2. ml-yacc logic-asgn1.yacc
3. sml
4. use "logic_asgn1_loader.sml";
5. flasl2valid(<input file name>);


The output file generated tells in the first line whether the formula is valid or invalid. In the subsequent lines, it tells truth assignments for the atoms in the input argument. If a truth assignment for some atom is not present, then you can assign them either value of your choice.