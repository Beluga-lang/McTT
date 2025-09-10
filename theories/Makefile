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

ROCQMAKEFILE := RocqMakefile.mk
COQPROJECTFILE := _CoqProject
PARSERBASE := Parser.ml
POSTPARSERBASE := Entrypoint.ml
PARSERFILE := ../driver/extracted/$(PARSERBASE)
POSTPARSERFILE := ../driver/extracted/$(POSTPARSERBASE)
ROCQPARSERFILE := $(patsubst %.vy,%.v,$(shell find ./ -name '*.vy'))
ROCQFILES := $(sort $(shell find ./ -name '*.v') $(ROCQPARSERFILE))

.PHONY: all
all: $(ROCQMAKEFILE)
	@+$(MAKE) -j "${NPROCS}" -f "$(ROCQMAKEFILE)" all

.PHONY: clean
clean: $(ROCQMAKEFILE)
	@+$(MAKE) -f "$(ROCQMAKEFILE)" cleanall
	@echo "CLEAN $(ROCQPARSERFILE) $(PARSERBASE) $(patsubst %.ml,%.mli,$(PARSERBASE)) $(PARSERFILE) $(patsubst %.ml,%.mli,$(PARSERFILE))"
	@rm -f "$(ROCQPARSERFILE)" "$(PARSERBASE)" "$(patsubst %.ml,%.mli,$(PARSERBASE))" "$(PARSERFILE)" "$(patsubst %.ml,%.mli,$(PARSERFILE))"
	@echo "CLEAN $(POSTPARSERBASE) $(patsubst %.ml,%.mli,$(POSTPARSERBASE)) $(POSTPARSERFILE) $(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@rm -f "$(POSTPARSERBASE)" "$(patsubst %.ml,%.mli,$(POSTPARSERBASE))" "$(POSTPARSERFILE)" "$(patsubst %.ml,%.mli,$(POSTPARSERFILE))"
	@echo "CLEAN $(ROCQMAKEFILE) $(ROCQMAKEFILE).conf"
	@rm -f "$(ROCQMAKEFILE)" "$(ROCQMAKEFILE).conf"

.PHONY: update_CoqProject
update_CoqProject: clean
	(echo "-R . Mctt"; \
        echo ""; \
        echo "-arg -w -arg -cast-in-pattern,-notation-overridden"; \
        echo ""; \
        echo -e "$(subst $(space),\n,$(ROCQFILES))") > "$(COQPROJECTFILE)"

.PHONY: force
force: ;

$(ROCQMAKEFILE): $(COQPROJECTFILE)
	rocq makefile -f "$?" -o "$@"

$(COQPROJECTFILE): ;

%: $(ROCQMAKEFILE) force
	@+$(MAKE) -f "$(ROCQMAKEFILE)" "$@"
