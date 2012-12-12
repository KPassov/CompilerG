#!/bin/bash

set -e # Die on first error.
# set -v # Output commands as they are executed.


# builds the Symbol Table
mosmlc -c SymTab.sml

# generates the SML sources for the lexer  
mosmllex Lexer.lex

# generates the SML sources for the parser 
mosmlyac -v Parser.grm

mosmlc -c Fasto.sml

# builds the parser (-liberal to avoid a "compliance warning")
mosmlc -liberal -c Parser.sig Parser.sml

# builds the lexer
mosmlc -c Lexer.sml

# builds the Interpreter
mosmlc -c Interpret.sig Interpret.sml

# builds MIPs
mosmlc -c Mips.sml

# build Register Allocator
mosmlc -c RegAlloc.sig RegAlloc.sml

# builds the Compiler
mosmlc -c Compiler.sig Compiler.sml

# builds the type checker
mosmlc -c Type.sig Type.sml

# builds the optimizer
mosmlc -c Optimization.sml

# builds the rest of the compiler
mosmlc -o FastoC FastoC.sml

# put FastoC in the main folder
mkdir -p ../BIN
mv FastoC ../BIN

# clean up
rm -f Compiler.u*
rm -f FastoC.u*
rm -f Interpret.u*
rm -f Mips.u*
rm -f Optimization.u*
rm -f RegAlloc.u*
rm -f SymTab.u*
rm -f Type.u*
rm -f *~
echo done
#################################
## use from command line:
##    $ mosml SeeSyntax.sml
## to see the AbSyn
#################################

##################################
## to run mips simulator
## java -jar Mars_4_2.jar program.asm
##################################

##################################
## fibo(10) = 89; fibo(11) = 144
##################################
