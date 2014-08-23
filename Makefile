.PHONY: software-foundations concrete-semantics

software-foundations:
	$(MAKE) -C $@ validate

concrete-semantics:
	cd $@ && isabelle build -D . -v
