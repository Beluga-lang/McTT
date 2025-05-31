NPROCS := 1
OS := $(shell uname)
export NPROCS

ifeq ($J,)

ifeq ($(OS),Linux)
  NPROCS := $(shell grep -c ^processor /proc/cpuinfo)
else ifeq ($(OS),Darwin)
  NPROCS := $(shell sysctl -n hw.ncpu.)
endif # $(OS)

else
  NPROCS := $J
endif # $J

empty :=
space := $(empty) $(empty)

MENHIR := menhir

COQMAKEFILE := CoqMakefile.mk
COQPROJECTFILE := _CoqProject
PARSERBASE := Parser.ml
POSTPARSERBASE := Entrypoint.ml
PARSERFILE := ../driver/extracted/$(PARSERBASE)
POSTPARSERFILE := ../driver/extracted/$(POSTPARSERBASE)
COQPARSERFILE := $(patsubst %.vy,%.v,$(shell find ./ -name '*.vy'))
COQFILES := $(sort $(shell find ./ -name '*.v') $(COQPARSERFILE))

.PHONY: all
all: $(COQMAKEFILE)
	@+$(MAKE) -j "${NPROCS}" -f "$(COQMAKEFILE)" all

.PHONY: clean
clean: $(COQMAKEFILE)
	@+$(MAKE) -f "$(COQMAKEFILE)" cleanall
	@echo "CLEAN $(COQPARSERFILE) $(PARSERBASE) $(patsubst %.ml,%.mli,$(PARSERBASE)) $(PARSERFILE) $(patsubst %.ml,%.mli,$(PARSERFILE))"
	@rm -f "$(COQPARSERFILE)" "$(PARSERBASE)" "$(patsubst %.ml,%.mli,$(PARSERBASE))" "$(PARSERFILE)" "$(patsubst %.ml,%.mli,$(PARSERFILE))"
	@echo "CLEAN $(POSTPARSERBASE) $(patsubst %.ml,%.mli,$(POSTPARSERBASE)) $(POSTPARSERFILE) $(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@rm -f "$(POSTPARSERBASE)" "$(patsubst %.ml,%.mli,$(POSTPARSERBASE))" "$(POSTPARSERFILE)" "$(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@echo "CLEAN $(COQMAKEFILE) $(COQMAKEFILE).conf"
	@rm -f "$(COQMAKEFILE)" "$(COQMAKEFILE).conf"

.PHONY: update_CoqProject
update_CoqProject: clean
	(echo "-R . Mctt"; \
        echo ""; \
        echo "-arg -w -arg -cast-in-pattern,-notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(COQFILES))") > "$(COQPROJECTFILE)"

.PHONY: force
force: ;

$(COQMAKEFILE): $(COQPROJECTFILE)
	$(COQBIN)coq_makefile -f "$?" -o "$@"

$(COQPROJECTFILE): ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f "$(COQMAKEFILE)" "$@"
