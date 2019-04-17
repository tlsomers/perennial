Q:=@
SRC_DIRS := 'src' $(shell test -d 'vendor' && echo 'vendor') $(shell test -d 'external' && echo 'external')
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))
TEST_VO := $(TEST_VFILES:.v=.vo)

COQ_WARN_LIST := -notation-overridden\
-redundant-canonical-projection\
-several-object-files\
-implicit-core-hint-db\
-undeclared-scope\
-solve_obligation_error\
-auto-template\
-ambiguous-paths

# A literal space.
space :=
space +=
# A literal comma
comma := ,

# Joins elements of a list with a comma
join-with-comma = $(subst $(space),$(comma),$(strip $1))

COQ_ARGS = -w $(call join-with-comma,$(COQ_WARN_LIST)) $(shell cat '_CoqProject')

default: src/ShouldBuild.vo

all: $(VFILES:.v=.vo)
test: $(TEST_VO) $(VFILES:.v=.vo)

_CoqProject: _CoqExt libname $(wildcard vendor/*) $(wildcard external/*)
	@echo "-R src $$(cat libname)" > $@
	@cat _CoqExt >> $@
	$(Q)for libdir in $(wildcard vendor/*); do \
	libname=$$(cat $$libdir/libname); \
	if [ $$? -ne 0 ]; then \
	  echo "Do you need to run git submodule update --init --recursive?" 1>&2; \
		exit 1; \
	fi; \
	echo "-R $$libdir/src $$(cat $$libdir/libname)" >> $@; \
	done
	@echo "_CoqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	$(Q)coqc $(COQ_ARGS) $< -o $@

.PHONY: ci
ci: src/ShouldBuild.vo $(TEST_VO)

clean:
	@echo "CLEAN vo glob aux"
	$(Q)rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob)
	$(Q)find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -f _CoqProject .coqdeps.d

.PHONY: default test clean
.DELETE_ON_ERROR:
