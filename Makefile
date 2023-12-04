include Makefile.config

DIRS=lib common $(ARCH) backend cfrontend driver \
  flocq/Core flocq/Prop flocq/Calc flocq/Appli \
	cparser cparser/validator cccommon cccfrontend

RECDIRS=lib common $(ARCH) backend cfrontend driver flocq cparser


COQINCLUDES= $(foreach d, $(RECDIRS), -R $(d) -as compcert.$(d)) \
	-R cccommon -as compcert.cccommon -R cccfrontend -as compcert.cccfrontend \
  -I $(ARCH) -as compcert.$(ARCH)

CAMLINCLUDES=$(patsubst %,-I %, $(DIRS)) -I extraction

MENHIR=menhir
COQC="$(COQBIN)coqc" -q $(COQINCLUDES)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
	-cflags -g \
  $(CAMLINCLUDES)
OCB_OPTIONS_CHECKLINK=\
  $(OCB_OPTIONS) \
  -I checklink \
  -use-ocamlfind
# OCB_OPTIONS_CLIGHTGEN=\
#   $(OCB_OPTIONS) \
#   -I exportclight

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

FLOCQ=\
  Fcore_Raux.v Fcore_Zaux.v Fcore_defs.v Fcore_digits.v                     \
  Fcore_float_prop.v Fcore_FIX.v Fcore_FLT.v Fcore_FLX.v                    \
  Fcore_FTZ.v Fcore_generic_fmt.v Fcore_rnd.v Fcore_rnd_ne.v                \
  Fcore_ulp.v Fcore.v                                                       \
  Fcalc_bracket.v Fcalc_digits.v Fcalc_div.v Fcalc_ops.v                    \
  Fcalc_round.v Fcalc_sqrt.v                                                \
  Fprop_div_sqrt_error.v Fprop_mult_error.v Fprop_plus_error.v              \
  Fprop_relative.v Fprop_Sterbenz.v                                         \
  Fappli_rnd_odd.v Fappli_IEEE.v Fappli_IEEE_bits.v Fappli_IEEE_extra.v

# General-purpose libraries (in lib/)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Archi.v Floats.v Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Unit.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Align.v Alloc.v MemReserve.v IntFacts.v Errors.v AST.v EventsGeneric.v Events.v Globalenvs.v Values.v Values_symbolictype.v ExprEval.v NormaliseSpec.v Normalise.v Values_symbolic.v Memdata.v Memtype.v Memory.v MemRel.v \
  Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v Equivalences.v Memperm.v Compat.v CompatForgetInj.v ForgetNorm.v Tactics.v

CCCOMMON=CCEvents.v CCGlobalenvs.v CCMemdata.v CCMemtype.v CCMemory.v CCSmallstep.v CCBehaviors.v CCDeterminism.v

# Back-end modules (in backend/, $(ARCH)/, $(ARCH)/$(VARIANT))

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v Selection.v \
  SelectDiv.v SelectLong.v \
  SelectOpproof.v SelectDivproof.v SelectLongproof.v Selectionproof.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Registers.v RTL.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Bounds.v Stacklayout.v \
  Mach.v \
  Renumber.v Renumberproof.v \
  Kildall.v \
  RTLtyping.v \
  Allocation.v Allocproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v \
  Liveness.v ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v SameEvalCmp.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Stacking.v StackingInject.v Stackingproof.v


  
# C front-end modules (in cfrontend/)

CFRONTEND=SimplLocals.v SimplLocalsproof.v Ctypes.v Cop.v Csyntax.v	\
  Csem.v Cstrategy.v Cexec.v Initializers.v VarSort.v SimplExpr.v		\
  SimplExprspec.v SimplExprproof.v ClightSyntax.v CopGeneric.v Clight.v		\
  Clight2.v Clighteq.v ClightRel.v Cshmgen.v Cshmgenproof.v Csharpminor.v Cminorgen.v	\
  Cminorgenproof.v CopSyntax.v

CCCFRONTEND=CCCtypes.v CCClight.v

# LR(1) parser validator

PARSERVALIDATOR=Alphabet.v Interpreter_complete.v Interpreter.v \
  Validator_complete.v Automaton.v Interpreter_correct.v Main.v \
  Validator_safe.v Grammar.v Interpreter_safe.v Tuples.v

# Parser

PARSER=Cabs.v Parser.v

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# All source files

FILES=$(LIB) $(COMMON) $(CFRONTEND) $(BACKEND) $(DRIVER) $(FLOCQ) \
  $(PARSERVALIDATOR) $(PARSER) $(CCCFRONTEND) $(CCCOMMON)

# Symbolic links vs. copy

ifneq (,$(findstring CYGWIN,$(shell uname -s)))
SLN=cp
else
SLN=ln -s
endif

all:
	$(MAKE) proof
	$(MAKE) extraction
	cd extraction && /bin/bash patch_memory_trace.sh && cd ..
	$(MAKE) ccomp
	$(MAKE) runtime

version:
	$(COQC) -v

proof: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v # $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

ccomp: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && $(SLN) _build/driver/Driver.native ccomp 

ccomp.prof: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && $(SLN) _build/driver/Driver.p.native ccomp.prof

ccomp.byte: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.byte \
        && rm -f ccomp.byte && $(SLN) _build/driver/Driver.d.byte ccomp.byte

runtime:
	$(MAKE) -C runtime

cchecklink: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.native \
        && rm -f cchecklink && $(SLN) _build/checklink/Validator.native cchecklink

cchecklink.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.d.byte \
        && rm -f cchecklink.byte && $(SLN) _build/checklink/Validator.d.byte cchecklink.byte

# clightgen: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
# 	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.native \
#         && rm -f clightgen && $(SLN) _build/exportclight/Clightgen.native clightgen

# clightgen.byte: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
# 	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.d.byte \
#         && rm -f clightgen.byte && $(SLN) _build/exportclight/Clightgen.d.byte clightgen.byte

.PHONY: proof extraction ccomp ccomp.prof ccomp.byte cchecklink cchecklink.byte

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex doc/coq2html.mll

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod -w $*.v

driver/Configuration.ml: Makefile.config VERSION
	(echo let stdlib_path = "\"$(LIBDIR)\""; \
         echo let prepro = "\"$(CPREPRO)\""; \
         echo let asm = "\"$(CASM)\""; \
         echo let linker = "\"$(CLINKER)\""; \
         echo let arch = "\"$(ARCH)\""; \
         echo let model = "\"$(MODEL)\""; \
         echo let abi = "\"$(ABI)\""; \
         echo let system = "\"$(SYSTEM)\""; \
         echo let has_runtime_lib = $(HAS_RUNTIME_LIB); \
         echo let asm_supports_cfi = $(ASM_SUPPORTS_CFI); \
         version=`cat VERSION`; \
         echo let version = "\"$$version\"") \
        > driver/Configuration.ml

cparser/Parser.v: cparser/Parser.vy
	$(MENHIR) --coq cparser/Parser.vy

depend: $(FILES) # exportclight/Clightdefs.v
	$(COQDEP) $^ \
        | sed -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend

install:
	install -d $(BINDIR)
	install ./ccomp $(BINDIR)
	install -d $(LINKDIR)
ifeq ($(CCHECKLINK),true)
	install ./cchecklink $(BINDIR)
endif
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) -C runtime install
endif

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte cchecklink cchecklink.byte #clightgen clightgen.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	rm -f driver/Configuration.ml
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli
	rm -f tools/ndfun tools/*.cm? tools/*.o
	rm -f $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v backend/SelectDiv.v backend/SelectLong.v

PACKAGEABLE=$(FILES) configure Makefile VERSION runtime README default.nix \
	backend/PrintRTL.ml backend/Regalloc.ml backend/IRC.ml backend/XTL.ml backend/PrintXTL.ml backend/PrintLTL.ml backend/Splitting.ml \
	backend/PrintMach.ml backend/Unusedglob.ml backend/CMtypecheck.ml backend/CMparser.mly backend/CMlexer.mll backend/ValueAnalysisaux.ml \
	backend/Linearizeaux.ml backend/RTLgenaux.ml \
	backend/PrintAnnot.ml backend/PrintCminor.ml \
	cfrontend/C2C.ml cfrontend/CPragmas.ml cfrontend/PrintClight.ml cfrontend/PrintCsyntax.ml \
	common/Values_symbolic_aux.ml common/MaxAlignment.ml common/Memdataaux.ml common/PrintAST.ml common/PrintValues.ml \
	common/Sections.mli common/Sections.ml common/Switchaux.ml \
	common/SMTParser.mly common/SMTLexer.mll \
	cparser/*.ml cparser/*.mli cparser/Parser.vy cparser/pre_parser.mly cparser/pre_parser_aux.ml cparser/Lexer.mll \
	driver/Configuration.ml driver/Clflags.ml driver/Driver.ml driver/Interp.ml \
	extraction/extraction.v extraction/patch_memory_trace.sh extraction/patch.ml.donotremove extraction/patch.mli.donotremove \
	lib/Camlcoq.ml lib/Tokenize.mli lib/Tokenize.mll \
	doc/coq2html.js doc/coq2html.mll doc/coq2html.css .depend _tags \
	$(ARCH)/*.ml \
	$(ARCH)/extractionMachdep.v

package: $(PACKAGEABLE)
	cd .. && tar -zcf compcertS.tar.gz $(addprefix compcertS-itp17/,$^)

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk (coq 8.4.pl2):
# Integers.Int.Z_mod_modulus_range takes forever to check
# Floats.Float.double_of_bits_of_double takes forever to check
# AST.external_function gives "Failure: impredicative Type inductive type"
# Asm.instruction gives "Failure: impredicative Type inductive type"
# Mach.instruction gives "Failure: impredicative Type inductive type"
# UnionFind.UF.elt gives "Anomaly: Uncaught exception Reduction.NotConvertible"

check-proof: $(FILES)
	$(COQCHK) -admit Integers -admit Floats -admit AST -admit Asm -admit Mach -admit UnionFind Complements 

print-includes:
	@echo $(COQINCLUDES)

include .depend


FORCE:
