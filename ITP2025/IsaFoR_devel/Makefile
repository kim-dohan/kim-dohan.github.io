LIB=lib
SRC=src
THYS=thys
EX_DIR:=examples
EX_FILES:=$(shell ls $(EX_DIR)/*.proof.xml)
EX_FILES2:=$(shell ls $(EX_DIR)/*.cpf.xml)
TERMFUN=$(THYS)/TermFun
GENERATED=generated
HASKELL=Haskell
STATIC=
override GHC_ARGS := -package array -O2 -rtsopts -XRankNTypes $(GHC_ARGS) $(if $(STATIC), -static -optl-static -optl-pthread, )
OCAML=OCaml
SML=SML
SCALA=Scala
BUILD=build
XML=xml
VERSION=$(shell cat .version)
MINOR_VERSION=$(VERSION)
VERSION_DIR=archive/v$(VERSION)
CETA_DIR=CeTA-$(VERSION)
VERSION_DIR_CETA=$(VERSION_DIR)/$(CETA_DIR)
ARCHIVE=CeTA-$(VERSION).tgz
DOCKER_ARCHIVE=CeTA-docker-scripts.tgz
# MACINTEL = desktop rene
MACINTEL=pc6145-c703.uibk.ac.at
# MACARM = studio rene
MACARM=c703-pc-8a4b.uibk.ac.at
LOCAL_WWW=WWW
WWW=colo2-c703.uibk.ac.at
WWW_DIR=/home/www/colo1-c703/software/ceta
JAVA_RUNTIME=$(shell java -verbose 2>&1 | grep 'Opened.*rt\.jar' | sed 's/\[Opened \(.*\)\]/\1/')
ISABELLE=$(shell isabelle getenv -b ISABELLE_TOOL)
ISABELLE_BUILD=$(ISABELLE) build $(ISAFOR_BUILD_OPTS)
SCALA_LIBRARY_PATH=$(shell $(ISABELLE) getenv -b SCALA_HOME)/lib
HEAPS=$(shell $(ISABELLE) getenv -b ISABELLE_OUTPUT)
OK=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32m  OK  \0033[0m]"
OK_ASS=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32mOK ASS\0033[0m]"
ERROR=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[31mFAILED\0033[0m]"
MAKE=make --no-print-directory

# the following ugly check sets ISAFOR_BUILD_OPTS to "-d thys"
# if there is no QTRS session by default
ISAFOR_BUILD_OPTS:=$(shell $(ISABELLE) build -n -x QTRS Pure > /dev/null 2>&1 || echo -d thys)

default: isafor test

isafor: ceta isafor_no_ceta

all: ceta test termfun

remote_build: $(LIB)/remote_build.jar

$(BUILD)/Remote_Build.class: $(SRC)/remote_build.scala
	@if [ ! -e $(BUILD) ]; then mkdir $(BUILD); fi
	$(ISABELLE) scalac -d $(BUILD) $<

$(BUILD)/remote_build.jar: $(BUILD)/Remote_Build.class
	cd $(BUILD) && \
	  jar cevf Remote_Build remote_build.jar Remote_Build.class 'Remote_Build$$.class'

$(LIB)/remote_build.jar: $(BUILD)/remote_build.jar
	cp $< $@

deploy_src: $(VERSION_DIR)/$(ARCHIVE)
	scp $(VERSION_DIR)/$(ARCHIVE) $(WWW):$(WWW_DIR)/src
	scp $(VERSION_DIR_CETA)/README $(WWW):$(WWW_DIR)/src
	ssh $(WWW) "cd $(WWW_DIR); cd src; rm CeTA.tgz; ln -s $(ARCHIVE) CeTA.tgz"

deploy_binary: linux_arm linux_intel macos_intel macos_arm
	scp $(VERSION_DIR)/ceta_linux_intel $(WWW):$(WWW_DIR)/bin/linux_intel/ceta
	scp $(VERSION_DIR)/ceta_linux_arm $(WWW):$(WWW_DIR)/bin/linux_arm/ceta
	scp $(VERSION_DIR)/ceta_macos_intel $(WWW):$(WWW_DIR)/bin/macos_intel/ceta
	scp $(VERSION_DIR)/ceta_macos_arm $(WWW):$(WWW_DIR)/bin/macos_arm/ceta

deploy: deploy_binary deploy_src
	@echo 
	@echo "Please update index and version files on www"
	@echo 
	@echo "Don't forget to tag this version with mercurial"
	@echo "hg tag v$(MINOR_VERSION); hg push"

termfun:
	$(ISABELLE_BUILD) -g termfun

isafor_no_ceta:
	$(ISABELLE_BUILD) -g isafor

code: $(GENERATED)
	$(ISABELLE) getenv ISAFOR AFP && $(ISABELLE) export -d thys -x "*:**.hs" -p 3 -O generated/Haskell Code

cpf_23_code: $(GENERATED)
	$(ISABELLE) getenv ISAFOR AFP && $(ISABELLE) export -d thys -x "*:**.hs" -p 3 -O generated/Haskell CPF_2_to_3

pre_version: $(VERSION_DIR)/$(ARCHIVE)
	@echo "Tests of availability of build machines"
	@echo "Testing MACARM access: "
	ssh $(MACARM) "echo ok"
	@echo "Testing MACINTEL access: "
	ssh $(MACINTEL) "echo ok"
	@echo "Testing Docker availability: "
	ssh $(MACARM) 'bash -l -c "docker ps > /dev/null"' && echo "ok"
	ssh $(MACINTEL) 'bash -l -c "docker ps > /dev/null"' && echo "ok"
	@echo "Testing WWW access: "
	ssh $(WWW) "echo ok"
	@$(OK)

version: macos_arm macos_intel linux_arm linux_intel

macos_arm: pre_version
	@echo "Building MAC-OS X binary for arm machines"
	scp $(VERSION_DIR)/$(ARCHIVE) $(MACARM):
	ssh $(MACARM) "tar xzf $(ARCHIVE); cd $(CETA_DIR); rm -f ceta; make test"
	scp $(MACARM):$(CETA_DIR)/ceta $(VERSION_DIR)/ceta_macos_arm
	@$(OK)

macos_intel: pre_version
	@echo "Building MAC-OS X binary for Intel machines"
	scp $(VERSION_DIR)/$(ARCHIVE) $(MACINTEL):
	ssh $(MACINTEL) "tar xzf $(ARCHIVE); cd $(CETA_DIR); rm -f ceta; make"
	scp $(MACINTEL):$(CETA_DIR)/ceta $(VERSION_DIR)/ceta_macos_intel
	@$(OK)

linux_arm: macos_arm
	@echo "Building static Linux ARM binary via docker"
	tar czvf $(VERSION_DIR)/$(DOCKER_ARCHIVE) docker-scripts
	scp $(VERSION_DIR)/$(DOCKER_ARCHIVE) $(MACARM):
	ssh $(MACARM) "cd $(CETA_DIR); tar xzvf ../$(DOCKER_ARCHIVE); rm -f ceta;  bash -l -c docker-scripts/build-docker-static.sh"
	scp $(MACARM):$(CETA_DIR)/ceta $(VERSION_DIR)/ceta_linux_arm
	@$(OK)

linux_intel: macos_intel
	@echo "Building static Linux Intel binary via docker"
	tar czvf $(VERSION_DIR)/$(DOCKER_ARCHIVE) docker-scripts
	scp $(VERSION_DIR)/$(DOCKER_ARCHIVE) $(MACINTEL):
	ssh $(MACINTEL) "cd $(CETA_DIR); tar xzvf ../$(DOCKER_ARCHIVE); rm -f ceta;  bash -l -c docker-scripts/build-docker-static.sh"
	scp $(MACINTEL):$(CETA_DIR)/ceta $(VERSION_DIR)/ceta_linux_intel
	@$(OK)
    

$(VERSION_DIR)/$(ARCHIVE): .version $(LOCAL_WWW)/*
#	sed -i 's/IsaFoR:.*/IsaFoR:   v$(VERSION)/' $(LOCAL_WWW)/README
	@rm -rf $(VERSION_DIR)
	@mkdir -p $(VERSION_DIR)
	@mkdir -p $(VERSION_DIR_CETA)/$(XML)
	@mkdir -p $(VERSION_DIR_CETA)/$(SRC)/$(HASKELL)
	@cp -r $(THYS) $(VERSION_DIR_CETA)/$(THYS)
	@cp -r $(EX_DIR) COPYING COPYING.LESSER $(VERSION_DIR_CETA) 
	@cp $(XML)/cpf3.xsd $(XML)/lts.xsd $(VERSION_DIR_CETA)/$(XML)
	@sed -e "s/putStrLn version/putStrLn \"$(VERSION)\"/" $(SRC)/$(HASKELL)/Main.hs >$(VERSION_DIR_CETA)/$(SRC)/$(HASKELL)/Main.hs
	@cp -r $(GENERATED) $(VERSION_DIR_CETA)/
	@cp $(VERSION_DIR_CETA)/$(SRC)/$(HASKELL)/Main.hs $(VERSION_DIR_CETA)/$(GENERATED)/$(HASKELL)/
	@cp $(LOCAL_WWW)/* $(VERSION_DIR_CETA)
	@echo "Building and testing"
	(cd $(VERSION_DIR_CETA); make test)
	@$(OK)
	@echo "Cleaning compiled files"
	(cd $(VERSION_DIR_CETA); make clean)
	@$(OK)
	@echo "Creating sources"
	(cd $(VERSION_DIR); tar czvf $(ARCHIVE) $(CETA_DIR))
	@$(OK)

test:
	@echo "Testing examples"
	@echo
	@for i in $(EX_FILES); do \
	   echo $$i; \
	   ./ceta $$i > /dev/null 2> /dev/null ;  if [ $$? != 0 ]; then $(ERROR); else $(OK); fi; \
	done 
	@echo "   "
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

$(GENERATED):
	@echo "Creating directory '$(GENERATED)'"
	@mkdir $(GENERATED)
	@$(OK)
	@echo "Creating directory '$(GENERATED)/$(HASKELL)'"
	@mkdir $(GENERATED)/$(HASKELL)
	@$(OK)

ceta: $(GENERATED) code
	@$(MAKE) haskell

cetad: $(GENERATED) code
	@$(MAKE) haskell_debug

all_of_thys: admin/generate_All_of_Theories.sh
	./admin/generate_All_of_Theories.sh

$(BUILD)/Main.hs: $(SRC)/$(HASKELL)/Main.hs
	@if [ ! -e $(BUILD) ]; then mkdir $(BUILD); fi
	@echo "Copying main file into '$(BUILD)'"
	@cp $< $@
	@$(OK)

cpf2_to_3.sh: $(SRC)/cpf2_to_3.sh cpf2_to_3_phase_1
	@cp $(SRC)/cpf2_to_3.sh .

cpf2_to_3_phase_1: $(SRC)/$(HASKELL)/Main_CPF_2_to_3.hs $(GENERATED)/$(HASKELL) cpf_23_code
	@echo "Copying generated source files into '$(BUILD)'"
	@cp $(GENERATED)/$(HASKELL)/* $(BUILD)
	@cp $(SRC)/$(HASKELL)/Main_CPF_2_to_3.hs $(BUILD)
	@$(OK)
	@echo "Compiling 'cpf_2_to_3'"
	cd $(BUILD) && ghc $(GHC_ARGS) --make Main_CPF_2_to_3 -o cpf2_to_3_phase_1
	@cp $(BUILD)/cpf2_to_3_phase_1 .
	@$(OK)


haskell: $(BUILD)/Main.hs $(GENERATED)/$(HASKELL)
	@echo "Copying generated source files into '$(BUILD)'"
	@cp $(GENERATED)/$(HASKELL)/* $(BUILD)
	@# replace \\ by \n because of String.literal problem
	@sed -e 's/\\\\/\\n/g' $(GENERATED)/$(HASKELL)/Ceta.hs >$(BUILD)/Ceta.hs 
	@$(OK)
	@echo "Compiling 'ceta'"
	cd $(BUILD) && ghc $(GHC_ARGS) --make Main -o ceta
	@cp $(BUILD)/ceta .
	@$(OK)

clean:
	@echo "Cleaning directory"
	@for f in $(BUILD); do \
	  if [ -e $$f ]; then rm -rf $$f; fi \
	done
	@$(OK)

veryclean:
	@$(MAKE) clean
	@echo "Purging directory"
	@for f in $(GENERATED) ceta; do \
	  if [ -e $$f ]; then rm -rf $$f; fi \
	done
	@$(OK)

cleanall:
	@$(MAKE) veryclean
	@echo "Purging heap files"
	@for f in $(HEAPS)/isafor_backup $(HEAPS)/isafor; do \
	  if [ -e $$f ]; then rm -rf $$f; fi \
	done
	@$(OK)

haskell_debug: $(SRC)/$(HASKELL)/Main.hs $(SRC)/$(HASKELL)/DebugCode.hs \
  $(GENERATED)/$(HASKELL)
	@if [ ! -e $(BUILD) ]; then mkdir $(BUILD); fi
	@echo "Copying generated source files into '$(BUILD)'"
	@cp $(GENERATED)/$(HASKELL)/* $(BUILD)/
	@$(OK)
	@echo "Copying main file into '$(BUILD)'"
	@cp $(SRC)/$(HASKELL)/Main.hs $(SRC)/$(HASKELL)/DebugCode.hs $(BUILD)/
	@$(OK)
	@sed -f $(SRC)/$(HASKELL)/cetad.sed $(GENERATED)/$(HASKELL)/Ceta.hs >$(BUILD)/Ceta.hs
	@echo "Compiling Haskell sources"
	@cd $(BUILD) && ghc $(GHC_ARGS) --make Main -o cetad > /dev/null 2>&1
	@$(OK)
	@echo "Generating 'cetad' (debugging version of 'ceta')"
	@cp $(BUILD)/cetad .
	@$(OK)

examples/cpfHTML.full.xsl: examples/cpfHTML.xsl examples/lts.xsl examples/include.xsl
	@xsltproc examples/include.xsl $< > $@

.PHONY: all clean code \
  deploy deploy_binary deploy_src \
  haskell haskell_debug remote_build isafor license linux64 macosx \
  normequiv ocaml pcp pre_version test version veryclean

