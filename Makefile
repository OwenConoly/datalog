.DEFAULT_GOAL := all

.PHONY: clean all atl datalog util

COQC ?= "$(COQBIN)coqc"

util: Makefile.coq
	$(MAKE) -C coqutil
	$(MAKE) -C verified-scheduling/src atl
	$(MAKE) -f Makefile.coq src/util/*.vo

datalog: util
	$(MAKE) -f Makefile.coq src/datalog/Datalog.vo src/datalog/Blocks.vo

atl: datalog
	$(MAKE) -C verified-scheduling/src low
	$(MAKE) -C verified-scheduling/src examples
	$(MAKE) -C verified-scheduling/src codegen
	$(MAKE) -C verified-scheduling/src padtest
	$(MAKE) -f Makefile.coq

COQ_MAKEFILE := $(COQBIN)coq_makefile -docroot datalog $(COQMF_ARGS)

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -C coqutil clean
	$(MAKE) -C verified-scheduling/src clean
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf
