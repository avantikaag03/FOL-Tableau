For Propositional Logic Tableau:

I have not explicitly created a makefile, since that can't be done in Windows. However, running my code is easy:
1. ml-lex logic_asgn1.lex
2. ml-yacc logic-asgn1.yacc
3. sml
4. use "logic_asgn1_loader.sml";
5. flasl2valid(<input file name>);


The output file generated tells in the first line whether the formula is valid or invalid. In the subsequent lines, it tells truth assignments for the atoms in the input argument. If a truth assignment for some atom is not present, then you can assign them either value of your choice.

For first order logic tableau:

1. use "logic_asgn3_fol.sml";
2. use "fol_tableau.sml";
3. open TABLEAU;
4. use "arg.sml";
5. output_tableau(<argument variable>);

The Unify list tells which formulas have been unified, and the Closing Path list tells which paths have been closed.
