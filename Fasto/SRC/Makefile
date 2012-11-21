# Makefile for Compilers lecture code
# here: source code (directory SRC)x

BINDIR=../BIN

MLC=mosmlc
MLI=mosml
MLLEX=mosmllex
MLYACC=mosmlyac -v

SMLSRC=Fasto.sml SymTab.sml Interpret.sml Type.sml Mips.sml RegAlloc.sml Compiler.sml FastoC.sml
SIGSRC=Interpret.sig RegAlloc.sig Compiler.sig Type.sig
EXTRASRC=Lexer.lex Parser.grm SeeSyntax
TESTSRC=fib.fo test.fo test.output

# generated files: Parser.sml, Parser.sig, Lexer.lex, all "uo" and "ui"
GENERATED=$(BINDIR)/FastoC Parser.sml Parser.sig Lexer.sml ${UIS} ${UOS}\
UIS=$(patsubst %.sig,%.ui,$(SIGSRC)) Parser.ui
UOS=$(patsubst %.sml,%.uo,$(SMLSRC)) Parser.uo Lexer.uo

all	: compiler interpreter typecheck main wipe 

main	: FastoC

FastoC 	: FastoC.uo ${UOS}
	mkdir -p $(BINDIR)
	$(MLC) FastoC.uo -o $(BINDIR)/$@


compiler : Compiler.uo

interpreter: Interpret.uo

typecheck : Type.uo

# Parser
Parser.sml Parser.sig: Parser.grm
	$(MLYACC) $<

#Lexer
Lexer.sml : Lexer.lex
	$(MLLEX) $<

# suffix rule for foo.sml -> foo.uo
%.uo	: %.sml
	$(MLC) -c $<
# suffix rule for foo.sml -> foo.uo
%.ui	: %.sig
	$(MLC) -c $<
# special rule for Parser.ui (-liberal to avoid a compliance warning)
Parser.ui: Parser.sig Fasto.uo
	$(MLC) -liberal -c $<

wipe:
	rm -f Compiler.u*
	rm -f FastoC.u*
	rm -f Interpret.u*
	rm -f Mips.u*
	rm -f Optimization.u*
	rm -f RegAlloc.u*
	rm -f SymTab.u*
	rm -f Type.u*
	rm -f *~

.PHONY	: clean
clean	:
	rm -f $(GENERATED) *.uo *.ui

########### generated dependencies (camlrunm $MOSML/tools/mosmldep)
Parser.uo: Parser.ui Fasto.uo 
Parser.ui: Fasto.uo 
Lexer.uo: Parser.ui 
RegAlloc.ui: Mips.uo 
RegAlloc.uo: RegAlloc.ui Mips.uo 
Interpret.ui: Fasto.uo 
Interpret.uo: Interpret.ui SymTab.uo Fasto.uo 
Type.ui: Fasto.uo 
Type.uo: Type.ui SymTab.uo Fasto.uo
Optimization.uo: SymTab.uo Fasto.uo
Compiler.ui: Mips.uo Fasto.uo 
Compiler.uo: Compiler.ui Mips.uo SymTab.uo Fasto.uo Type.ui RegAlloc.ui 
FastoC.uo: Parser.ui Compiler.ui Mips.uo Lexer.uo Fasto.uo Optimization.uo Interpret.ui Type.ui

