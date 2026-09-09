.PHONY: all clean clean-util distclean default watch generate plugin plugin-inline-print-check \
	evaluate-translated-examples evaluate-translated-add-one \
	evaluate-translated-choose-and-add evaluate-translated-evaluation-traits \
	evaluate-translated-let-mut evaluate-translated-ruint

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)
PLUGIN_INLINE_PRINT_TEST := plugin/test_inline_print.v
# The expected output is version-sensitive (scope-key printing and lemma
# re-exports changed after 9.2); select it alongside the compat shim below.
PLUGIN_INLINE_PRINT_EXPECTED := plugin/test_inline_print.expected
PLUGIN_INLINE_PRINT_OUTPUT := /tmp/rocqofrust-plugin-inline-print.out

PLUGIN_PACKAGES := \
	rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.parsing,rocq-runtime.pretyping,rocq-runtime.printing,rocq-runtime.proofs,rocq-runtime.tactics,rocq-runtime.vernac
EVALUATE_PACKAGES := rocq-runtime.kernel,zarith
EVALUATE_INCLUDES := -I evaluate -I evaluate/extracted
EXTRACTED_TY_ML := evaluate/extracted_ty.ml
EXTRACTED_TY_CMX := evaluate/extracted_ty.cmx

# Select the compat shim based on the Rocq version: the known-module
# registry was removed after 9.2.
ROCQ_LEGACY_MLTOP := $(shell coqc --version 2>/dev/null | grep -qE 'version (8\.|9\.[012]([^0-9]|$$))' && echo yes)
ifeq ($(ROCQ_LEGACY_MLTOP),yes)
PLUGIN_COMPAT_ML := plugin/compat/rocqofrust_plugin_compat_legacy.ml
else
PLUGIN_COMPAT_ML := plugin/compat/rocqofrust_plugin_compat_modern.ml
PLUGIN_INLINE_PRINT_EXPECTED := plugin/test_inline_print.dev.expected
endif

PLUGIN_ML := plugin/rocqofrust_plugin_compat.ml plugin/link_model.ml plugin/link_render.ml plugin/rocqofrust_link_plugin.ml

# Keep 'default' as the default goal: the rule below would otherwise
# become the first (and thus default) rule of the Makefile.
.DEFAULT_GOAL := default

# Always re-check (cheaply) so switching Rocq versions between builds
# picks the right shim; only copy on change to avoid rebuilds.
plugin/rocqofrust_plugin_compat.ml: $(PLUGIN_COMPAT_ML) FORCE
	@cmp -s $< $@ || cp $< $@

FORCE:

TRANSLATED_ADD_ONE_VO := examples/default/examples/custom/evaluate/translated_add_one.vo
TRANSLATED_ADD_ONE_EXTRACTED := evaluate/extracted/translated_add_one
TRANSLATED_ADD_ONE_BINARY := /tmp/rocqofrust-translated-add-one
TRANSLATED_CHOOSE_AND_ADD_VO := examples/default/examples/custom/evaluate/translated_choose_and_add.vo
TRANSLATED_CHOOSE_AND_ADD_EXTRACTED := evaluate/extracted/translated_choose_and_add
TRANSLATED_CHOOSE_AND_ADD_BINARY := /tmp/rocqofrust-translated-choose-and-add
TRANSLATED_EVALUATION_TRAITS_VO := examples/default/examples/custom/evaluate/translated_evaluation_traits.vo
TRANSLATED_EVALUATION_TRAITS_EXTRACTED := evaluate/extracted/translated_evaluation_traits
TRANSLATED_EVALUATION_TRAITS_BINARY := /tmp/rocqofrust-translated-evaluation-traits
TRANSLATED_LET_MUT_VO := examples/default/examples/custom/evaluate/translated_let_mut.vo
TRANSLATED_LET_MUT_EXTRACTED := evaluate/extracted/translated_let_mut
TRANSLATED_LET_MUT_BINARY := /tmp/rocqofrust-translated-let-mut
TRANSLATED_RUINT_VO := ruint/evaluate/lib.vo
TRANSLATED_RUINT_EXTRACTED := evaluate/extracted/ruint
TRANSLATED_RUINT_BINARY := /tmp/rocqofrust-translated-ruint

default: all

plugin: plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs

plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs: $(PLUGIN_ML) plugin/rocqofrust_link_plugin/META
	mkdir -p plugin/rocqofrust_link_plugin
	ocamlfind ocamlopt -I plugin -package $(PLUGIN_PACKAGES) -linkall -shared $(PLUGIN_ML) -o $@

plugin-inline-print-check: plugin $(PLUGIN_INLINE_PRINT_TEST) $(PLUGIN_INLINE_PRINT_EXPECTED)
	@echo "COQC plugin inline print $(PLUGIN_INLINE_PRINT_TEST)"
	@coqc -R . RocqOfRust -I plugin -impredicative-set $(PLUGIN_INLINE_PRINT_TEST) > $(PLUGIN_INLINE_PRINT_OUTPUT)
	@diff -u $(PLUGIN_INLINE_PRINT_EXPECTED) $(PLUGIN_INLINE_PRINT_OUTPUT)

evaluate-translated-examples: evaluate-translated-add-one evaluate-translated-choose-and-add \
	evaluate-translated-evaluation-traits evaluate-translated-let-mut \
	evaluate-translated-ruint

$(EXTRACTED_TY_CMX): $(EXTRACTED_TY_ML)
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -c $<

evaluate-translated-add-one: $(TRANSLATED_ADD_ONE_VO) $(EXTRACTED_TY_CMX)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_add_one.v
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_ADD_ONE_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_ADD_ONE_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -linkpkg \
		$(EVALUATE_INCLUDES) $(EXTRACTED_TY_CMX) \
		$(TRANSLATED_ADD_ONE_EXTRACTED).cmx \
		-o $(TRANSLATED_ADD_ONE_BINARY)
	@$(TRANSLATED_ADD_ONE_BINARY)
	@echo "Translated add_one(41) evaluated to 42."

evaluate-translated-choose-and-add: $(TRANSLATED_CHOOSE_AND_ADD_VO) $(EXTRACTED_TY_CMX)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_choose_and_add.v
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -linkpkg \
		$(EVALUATE_INCLUDES) $(EXTRACTED_TY_CMX) \
		$(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).cmx \
		-o $(TRANSLATED_CHOOSE_AND_ADD_BINARY)
	@$(TRANSLATED_CHOOSE_AND_ADD_BINARY)
	@echo "Translated choose_and_add(true, (10, 20), 5) evaluated to 15."

evaluate-translated-evaluation-traits: $(TRANSLATED_EVALUATION_TRAITS_VO) $(EXTRACTED_TY_CMX)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_evaluation_traits.v
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_EVALUATION_TRAITS_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_EVALUATION_TRAITS_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -linkpkg \
		$(EVALUATE_INCLUDES) $(EXTRACTED_TY_CMX) \
		$(TRANSLATED_EVALUATION_TRAITS_EXTRACTED).cmx \
		-o $(TRANSLATED_EVALUATION_TRAITS_BINARY)
	@$(TRANSLATED_EVALUATION_TRAITS_BINARY)
	@echo "Translated evaluation_traits::compute() evaluated to 41."

evaluate-translated-let-mut: $(TRANSLATED_LET_MUT_VO) $(EXTRACTED_TY_CMX)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_let_mut.v
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_LET_MUT_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_LET_MUT_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -linkpkg \
		$(EVALUATE_INCLUDES) $(EXTRACTED_TY_CMX) \
		$(TRANSLATED_LET_MUT_EXTRACTED).cmx \
		-o $(TRANSLATED_LET_MUT_BINARY)
	@$(TRANSLATED_LET_MUT_BINARY)
	@echo "Translated let_mut() evaluated to 6."

evaluate-translated-ruint: $(TRANSLATED_RUINT_VO) $(EXTRACTED_TY_CMX)
	coqc -R . RocqOfRust -I plugin -impredicative-set ruint/evaluate/lib.v
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_RUINT_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) \
		$(EVALUATE_INCLUDES) -c $(TRANSLATED_RUINT_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package $(EVALUATE_PACKAGES) -linkpkg \
		$(EVALUATE_INCLUDES) $(EXTRACTED_TY_CMX) \
		$(TRANSLATED_RUINT_EXTRACTED).cmx \
		-o $(TRANSLATED_RUINT_BINARY)
	@$(TRANSLATED_RUINT_BINARY)
	@echo "Translated ruint arithmetic, Uint, mutation, and loop cases passed."

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
RocqMakefile: plugin $(VFILES) blacklist.txt _RocqProject
	@coq_makefile -f _RocqProject -o $@ $(VFILES)

MAKEROCQ := +$(MAKE) -f RocqMakefile

%.vo: plugin RocqMakefile %.v
	$(MAKEROCQ) $@

all: plugin RocqMakefile
	$(MAKEROCQ) all

clean-rocq: RocqMakefile
	$(MAKEROCQ) clean

clean-util:
	rm -f *RocqMakefile*

clean: clean-rocq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean

watch:
	while true; do \
		inotifywait -e modify $(VFILES) Makefile; \
		make -k -j3; \
	done

GENERATE_FILES := $(shell find . -type f -name "generate.py")

generate: $(GENERATE_FILES)
	@for file in $(GENERATE_FILES); do \
		echo "python $$file"; \
		python $$file; \
	done
