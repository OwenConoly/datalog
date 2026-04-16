.DEFAULT_GOAL := all

.PHONY: clean all util datalog atl_to_datalog

COQC ?= "$(COQBIN)coqc"

COQ_MAKEFILE := $(COQBIN)coq_makefile -docroot datalog $(COQMF_ARGS)

UTIL_VOS    = $(patsubst %.v,%.vo,$(wildcard src/util/*.v))
DATALOG_VOS = $(patsubst %.v,%.vo,$(wildcard src/datalog/*.v))
ATL_VOS     = $(patsubst %.v,%.vo,$(wildcard src/atl/*.v))

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

util: Makefile.coq
	$(MAKE) -C coqutil
	$(MAKE) -C verified-scheduling/src low
	$(MAKE) -f Makefile.coq $(UTIL_VOS)

datalog: util
	$(MAKE) -f Makefile.coq $(DATALOG_VOS)

atl_to_datalog: datalog
	$(MAKE) -C verified-scheduling/src examples
	$(MAKE) -C verified-scheduling/src codegen
	$(MAKE) -C verified-scheduling/src padtest
	$(MAKE) -f Makefile.coq $(ATL_VOS)

all: atl_to_datalog

clean:: Makefile.coq
	$(MAKE) -C coqutil clean
	$(MAKE) -C verified-scheduling/src clean
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf

