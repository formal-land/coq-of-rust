.PHONY: all clean clean-util distclean default

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)

PYTHON_LINKS_FILES := $(shell find links -name "*.py")

OUTPUT_LINKS_FILES := $(PYTHON_LINKS_FILES:.py=.v)

# Default target
all: $(OUTPUT_FILES) links

default: all

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
CoqMakefile: $(VFILES) blacklist.txt
	@coq_makefile -f _CoqProject -o $@ $(VFILES)

MAKECOQ := +$(MAKE) -f CoqMakefile

%.vo: CoqMakefile %.v
	$(MAKECOQ) $@

all: CoqMakefile
	$(MAKECOQ) all

clean-coq: CoqMakefile
	$(MAKECOQ) clean

clean-util:
	rm -f *CoqMakefile*

clean: clean-coq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean

%.v: %.py links.py
	PYTHONPATH=. python $< > $@

links: $(OUTPUT_LINKS_FILES)
