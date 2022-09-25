.PHONY: coq ocaml all proofs clean clean_all clean_coq clean_ocaml clean_libs coq_depend extract clean_extracted ../c_primitives/c_lib.o

COMPCERT = $(wildcard compcert_coq/*/*.v)
MENHIR = $(wildcard MenhirLib/*.v)
FLOCQ = $(wildcard flocq/*/*.v)
LIBS = $(COMPCERT) $(MENHIR) $(FLOCQ)
FILES = common.v monad.v intpos.v IR.v primitives.v IRtoRTLblock.v backend.v jit.v liveness.v def_regs.v ASMinterpreter.v optimizer.v IRinterpreter.v monad_impl.v RTLblock.v flattenRTL.v assume_insertion.v anchor_insertion.v anchor_removal.v
PROOFS = mixed_sem.v input_proof.v IRtoRTLblock_proof.v backend_proof.v optimizer_proof.v sem_properties.v dynamic_proof.v internal_simulations.v monad_properties.v flattenRTL_proof.v customSmallstep.v customBehaviors.v jit_proof.v assume_insertion_proof.v anchor_insertion_proof.v

COQC=coqc -R compcert_coq compcert -R flocq Flocq -R MenhirLib MenhirLib
COQDEP=coqdep -R compcert_coq compcert -R flocq Flocq -R MenhirLib MenhirLib
CLIBS= c_lib.o stack.o heap.o prims.o codes.o
LINK_FLAGS= $(CLIBS:%.o= -lflag ../../c_primitives/%.o )
OCB_FLAGS = -tag bin_annot -I . -I extraction -I compcert_ocaml -I parsing -use-menhir -use-ocamlfind -lib unix $(LINK_FLAGS)
OCB=ocamlbuild $(OCB_FLAGS)

all: coq extract ocaml proofs

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $*.v

extract.vo: extract.v $(FILES:%.v=%.vo) $(LIBS:%.v=%.vo)
	@echo Creating extraction folder
	-@mkdir extraction
	@echo COQC extract.v
	@$(COQC) extract.v

coq_libs: $(LIBS:%.v=%.vo)

.depend: $(FILES) $(PROOFS) $(LIBS) extract.v
	@echo COQDEP: Generating dependencies
	@$(COQDEP) # ensure coqdep exists before writing to .depend
	@$(COQDEP) $^ > .depend

coq_depend: .depend

coq: coq_depend $(FILES:%.v=%.vo)

extract: coq extract.vo

proofs: coq $(PROOFS:%.v=%.vo)

../c_primitives/c_lib.o:
	$(MAKE) -C ../c_primitives

ocaml: ../c_primitives/c_lib.o
	@echo Building the OCaml Extracted JIT
	@$(OCB) main.native
	@cp compcert.ini _build/
	@mv main.native jit

test: test.ml
	@echo Building the OCaml Tests
	@$(OCB) test.native
	@cp compcert.ini _build/
	@mv test.native test

clean: clean_coq clean_extracted clean_prims clean_ocaml clean_tmp

clean_all: clean clean_libs

clean_coq:
	@echo Cleaning Coq compiled files
	-@rm .depend
	-@rm *.vo *.glob .*.aux *.vok *.vos

clean_libs:
	@echo Cleaning Coq compiled libraries
	-@rm compcert_coq/*/*.vo compcert_coq/*/*.glob compcert_coq/*/.*.aux compcert_coq/*/*.vok compcert_coq/*/*.vos
	-@rm MenhirLib/*.vo MenhirLib/*.glob MenhirLib/.*.aux MenhirLib/*.vok MenhirLib/*.vos
	-@rm flocq/*/*.vo flocq/*/*.glob flocq/*/.*.aux flocq/*/*.vok flocq/*/*.vos

clean_tmp:
	-@rm tmp.s
	-@rm linked.s
	-@rm linked.o

clean_extracted:
	@echo Cleaning Extracted files
	-@rm -R extraction

clean_prims:
	@echo Cleaning C Primitives
	$(MAKE) clean -C ../c_primitives

clean_ocaml:
	@echo Cleaning OCaml compiled files
	-@rm jit
	-@rm test
	-@rm -R _build

install-deps:
	opam pin add coqjit . --no-action # tell opam about a local "cogjit" package
	opam install --deps-only coqjit # then install its dependencies

-include .depend
