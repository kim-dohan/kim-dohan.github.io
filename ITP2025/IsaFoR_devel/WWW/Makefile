EX_FILES:=$(shell ls examples/*.proof.xml)
EX_FILES2:=$(shell ls examples/*.cpf.xml)
HASKELL=Haskell
STATIC=
override GHC_ARGS:= -O2 -package array -XRankNTypes  $(GHC_ARGS) $(if $(STATIC), -static -optl-static -optl-pthread, )
SRC=src
GENERATED=generated
OK=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32m  OK  \0033[0m]"
OK_ASS=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32mOK ASS\0033[0m]"
ERROR=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[31mFAILED\0033[0m]"
MAKE=make --no-print-directory

all: ceta
	@echo 'You can now check your proofs calling '
	@echo
	@echo 'ceta <cpfFile>'
	@echo
	@echo 'to test ceta just call "make test"'


test: ceta
	@echo "Testing examples"
	@echo
	@for i in $(EX_FILES); do \
	   echo $$i; \
	   ./ceta $$i > /dev/null 2> /dev/null ;  if [ $$? != 0 ]; then $(ERROR); else $(OK); fi; \
	done 
	@echo
	@echo "Testing examples (separate input, property, answer, and proof)"
	@echo
	@for cpf in $(EX_FILES2); do \
	   input=$${cpf%.cpf.xml}.input.xml; \
	   property=$${cpf%.cpf.xml}.property; \
	   answer=$${cpf%.cpf.xml}.answer; \
	   echo "$${cpf%.cpf.xml}.input.xml|.property|.answer|.cpf.xml" ; \
	   ./ceta --inputf $$input --propertyf $$property --answerf $$answer $$cpf > /dev/null 2> /dev/null ;  if [ $$? != 0 ]; then $(ERROR); else $(OK); fi; \
	done 
	@echo "   "

ceta:
	@$(MAKE) haskell

haskell:
	@echo "Compiling Haskell sources"
	@cd $(GENERATED)/$(HASKELL) && ghc $(GHC_ARGS) --make Main -o ceta > /dev/null 2>&1
	@$(OK)
	@echo "Generating 'ceta'"
	@mv $(GENERATED)/$(HASKELL)/ceta .
	@$(OK)

clean:
	@echo "Cleaning directory"
	@rm -f $(GENERATED)/$(HASKELL)/*.hi $(GENERATED)/$(HASKELL)/*.o
	@rm -f ceta
	@$(OK)

.PHONY: all clean haskell test
