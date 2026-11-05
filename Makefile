# =====================================================================
#  SUTRA — MaxSAT approximator
#  Author: Sethu Iyer (github.com/sethuiyer)
#
#  Two binaries:
#    sutra      the approximator (C99, no dependencies beyond libm)
#    sutracert  the independent certificate checker
#
#  Why -D_GNU_SOURCE: mkstemps() is a GNU extension, used for the
#  optional residual-subformula handoff.  Everything else is plain C99.
# =====================================================================
CC      ?= gcc
CFLAGS  ?= -O3 -std=c99 -march=native -D_GNU_SOURCE
LDLIBS  ?= -lm

all: sutra sutracert

# The engine is split into headers by concern:
#   sutra_nuwls.h  local search (the optimiser)
#   sutra_cert.h   parity detection + GF(2) + CDCL bridge (the prover)
#   cdcl_internal.h  the CDCL itself
sutra: sutra.c sutra_cert.h sutra_nuwls.h cdcl_internal.h navokoj_checkpoint.c navokoj_checkpoint.h
	$(CC) $(CFLAGS) -o $@ sutra.c navokoj_checkpoint.c $(LDLIBS)

# The checker deliberately shares no code with the solver: a certificate
# is only convincing if the verifier cannot inherit the producer's bugs.
sutracert: sutracert.c
	$(CC) -O2 -std=c99 -o $@ sutracert.c

test: all
	./tests.sh

clean:
	rm -f sutra sutracert

.PHONY: all test clean
