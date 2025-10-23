.DEFAULT_GOAL := all

.PHONY: clean all

COQC ?= "$(COQBIN)coqc"

all: Makefile.coq
	$(MAKE) -C coqutil
	$(MAKE) -C verified-scheduling/src low
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
