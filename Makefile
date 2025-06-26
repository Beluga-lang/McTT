.PHONY: all pretty-timed test coqdoc clean depgraphdoc

all:
	@$(MAKE) -C theories
	@dune build

pretty-timed:
	@$(MAKE) pretty-timed -C theories
	@dune build

pretty-timed-with-check:
	@$(MAKE) pretty-timed -C theories | tee ./theories.log | grep -e "COQC" -e "sys"
	@dune build

coqdoc:
	@${MAKE} coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
