COQC ?= coqc
COQMAKEFILE ?= coq_makefile
BUSYCOQ_DIR ?= ..
COQMFFLAGS := -Q $(BUSYCOQ_DIR) BusyCoq

# In the intended verify/CounterClass1 layout, the parent mapping already binds
# this directory to BusyCoq.CounterClass1.  The second mapping is only needed
# while this folder is built from a separate working tree for development.
ifneq ($(abspath .),$(abspath $(BUSYCOQ_DIR)/CounterClass1))
COQMFFLAGS += -Q . BusyCoq.CounterClass1
endif

ALLVFILES := $(sort $(wildcard *.v))

all: check

Makefile.coq: Makefile $(ALLVFILES)
	$(COQMAKEFILE) $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

check: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)

-include Makefile.coq

.PHONY: all check clean
