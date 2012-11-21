# Makefile for Compilers lecture code
## here: main Makefile, recursively calling make in SRCDIR

# directories:
## Sources
SRCDIR=SRC
## Test data
DATADIR=DATA
## Binaries (actually, only one...)
BINDIR=BIN

MLC=mosmlc
MLI=mosml
MLLEX=mosmllex
MLYACC=mosmlyac -v

# UNUSED for now
TESTSRCS=fib.fo test.fo
TESTCMP=test.output
TESTSRCSPATH=$(patsubst %.fo,$(DATADIR)/%,$(TESTSRCS))

# USED
COMPILEFILE=$(DATADIR)/fib
COMPILED=$(DATADIR)/fib.asm

# generated files, removed by clean target
GENERATED=$(COMPILED)

all	: FastoC compilation

compilation: FastoC $(COMPILED)

$(COMPILED)	: $(COMPILEFILE).fo FastoC
	$(BINDIR)/FastoC -c $(COMPILEFILE)

# the compiler
FastoC 	: 
	@make -C $(SRCDIR) compiler typecheck interpreter FastoC

.PHONY	: clean allclean
clean	:
	rm -f $(GENERATED)

allclean: clean
	@make -C SRC clean
