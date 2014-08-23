coq.mk: $(wildcard *.v)
	coq_makefile -install none -o $@ $^

include coq.mk

.PHONY: clean-mk
clean-mk:
	rm -f coq.mk

clean: clean-mk
