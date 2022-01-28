PACKAGES=str,num

# create directory if not exist
DIR_GUARD=@mkdir -p $(@D)

#Name of the final executable file to be generated
EX_NAME=coxs

# source folder
SOURCE_DIR=src
LOGIC_SOURCE_DIR=src/logic
LIB_SOURCE_DIR=src/lib

# binary folder for compilation
BIN_DIR=bin
LOGIC_BIN_DIR=bin/logic
LIB_BIN_DIR=bin/lib
RELEASE_DIR = release
LOGIC_RELEASE_DIR = release/logic
LIB_RELEASE_DIR = release/lib
OBJ_DIR=${SOURCE_DIR}
LOGIC_OBJ_DIR=${LOGIC_SOURCE_DIR}
LIB_OBJ_DIR=${LIB_SOURCE_DIR}

OCAMLC_FLAGS=-bin-annot -w -26  -I $(BIN_DIR) -I $(LOGIC_BIN_DIR) -I $(LIB_BIN_DIR)
OCAMLOPT_FLAGS=-bin-annot -w -26 -I $(RELEASE_DIR) -I $(LOGIC_RELEASE_DIR) -I $(LIB_RELEASE_DIR)
OCAMLDEP_FLAGS=-I $(SOURCE_DIR) -I $(LOGIC_SOURCE_DIR) -I $(LIB_SOURCE_DIR)


#Name of the files that are part of the project
MAIN_FILE=main

LOGIC_FILES=\
    lib intro formulas prop fol skolem fol_ex\

LIB_FILES=\
		expr utils\
		rule_preprocess stratification derivation\
		ast2sql\

TOP_FILES=\
		tools\
    parser lexer\
		calc \
		datalog2fol\
		satisfiability\
		preperation disjoint consistency view_common view_init view_evo view_ts\
		framework_tar framework1 framework2 framework\

FILES=\
    $(LOGIC_FILES:%=logic/%)\
		$(LIB_FILES:%=lib/%)\
    $(TOP_FILES)

.PHONY: all release clean depend annot
all: $(BIN_DIR)/$(EX_NAME) annot

#Rule for generating the final executable file
$(BIN_DIR)/$(EX_NAME): $(FILES:%=$(BIN_DIR)/%.cmo) $(BIN_DIR)/$(MAIN_FILE).cmo
	$(DIR_GUARD)
	ocamlfind ocamlc $(OCAMLC_FLAGS) -package $(PACKAGES) -thread -linkpkg $(FILES:%=$(BIN_DIR)/%.cmo) $(BIN_DIR)/$(MAIN_FILE).cmo -o $(BIN_DIR)/$(EX_NAME)

#Rule for compiling the main file
$(BIN_DIR)/$(MAIN_FILE).cmo: $(FILES:%=$(BIN_DIR)/%.cmo) $(SOURCE_DIR)/$(MAIN_FILE).ml
	$(DIR_GUARD)
	ocamlfind ocamlc $(OCAMLC_FLAGS) -package $(PACKAGES) -thread -o $(BIN_DIR)/$(MAIN_FILE) -c $(SOURCE_DIR)/$(MAIN_FILE).ml

#Special rules for creating the lexer and parser
$(SOURCE_DIR)/parser.ml $(SOURCE_DIR)/parser.mli: $(SOURCE_DIR)/parser.mly
	ocamlyacc $<
$(BIN_DIR)/parser.cmi:	$(SOURCE_DIR)/parser.mli
	$(DIR_GUARD)
	ocamlc $(OCAMLC_FLAGS) -o $(BIN_DIR)/parser -c $<
$(BIN_DIR)/parser.cmo:	$(SOURCE_DIR)/parser.ml $(BIN_DIR)/parser.cmi
	$(DIR_GUARD)
	ocamlc $(OCAMLC_FLAGS) -o $(BIN_DIR)/parser -c $<
$(SOURCE_DIR)/lexer.ml:	$(SOURCE_DIR)/lexer.mll
	ocamllex $<

#General rule for compiling
$(BIN_DIR)/%.cmi $(BIN_DIR)/%.cmo $(BIN_DIR)/%.cmt: $(SOURCE_DIR)/%.ml
	$(DIR_GUARD)
	ocamlfind ocamlc $(OCAMLC_FLAGS) -package $(PACKAGES) -thread -o $(BIN_DIR)/$* -c $<

annot: $(FILES:%=$(SOURCE_DIR)/%.cmt) $(MAIN_FILE:%=$(SOURCE_DIR)/%.cmt)

$(FILES:%=$(SOURCE_DIR)/%.cmt) $(MAIN_FILE:%=$(SOURCE_DIR)/%.cmt): $(LOGIC_FILES:%=$(LOGIC_BIN_DIR)/%.cmt) $(LIB_FILES:%=$(LIB_BIN_DIR)/%.cmt) $(TOP_FILES:%=$(BIN_DIR)/%.cmt) $(MAIN_FILE:%=$(BIN_DIR)/%.cmt)
	cp $(LOGIC_FILES:%=$(LOGIC_BIN_DIR)/%.cmt) $(LOGIC_SOURCE_DIR)/
	cp $(LIB_FILES:%=$(LIB_BIN_DIR)/%.cmt) $(LIB_SOURCE_DIR)/
	cp $(TOP_FILES:%=$(BIN_DIR)/%.cmt) $(SOURCE_DIR)/
	cp $(MAIN_FILE:%=$(BIN_DIR)/%.cmt) $(SOURCE_DIR)/

include depend

clean:
	rm -r -f $(BIN_DIR)/* $(RELEASE_DIR)/* $(SOURCE_DIR)/parser.mli $(SOURCE_DIR)/parser.ml $(SOURCE_DIR)/lexer.ml $(OBJ_DIR)/*.cmt $(LOGIC_OBJ_DIR)/*.cmt $(LIB_OBJ_DIR)/*.cmt $(OBJ_DIR)/*.cmti $(LOGIC_OBJ_DIR)/*.cmti $(LIB_OBJ_DIR)/*.cmti $(OBJ_DIR)/*.cmo $(LOGIC_OBJ_DIR)/*.cmo $(LIB_OBJ_DIR)/*.cmo $(OBJ_DIR)/*.cmi $(LOGIC_OBJ_DIR)/*.cmi $(LIB_OBJ_DIR)/*.cmi

depend:
	ocamlfind ocamldep $(OCAMLDEP_FLAGS) $(FILES:%=$(SOURCE_DIR)/%.ml) $(SOURCE_DIR)/lexer.mll $(SOURCE_DIR)/parser.mli |sed -e 's/$(SOURCE_DIR)/$(BIN_DIR)/g' > depend

release: $(RELEASE_DIR)/$(EX_NAME)


#parser.ml: parser.mly
#	ocamlyacc parser.mly
#	ocamlyacc $<

# parser.cmi:	parser.mli
#	ocamlc -bin-annot -w -26 -o parser -c $<

# parser.cmo:	parser.ml parser.cmi
#	ocamlc -bin-annot -w -26  -o parser -c $<

#lexer.ml: lexer.mll
#	ocamllex lexer.mll

#.PHONY: clean
#clean:
#	rm -f parser.ml parser.mli lexer.ml *.cmi *.cmx *.cmo *.cmt text2expr
