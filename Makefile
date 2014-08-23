.PHONY: software-foundations concrete-semantics

software-foundations:
	$(MAKE) -C $@

concrete-semantics:
	cd $@ && isabelle build -D . -v
