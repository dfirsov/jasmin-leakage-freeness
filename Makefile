TIMEOUT ?= 20

EXTRACTED_FILES = \
    proof/jasmin_extracts/W64_RejectionSamplingExtract.ec \
    proof/jasmin_extracts/W64_RejectionSamplingExtract_ct.ec

PROOF_FILES += $(EXTRACTED_FILES)
PROOF_FILES += $(wildcard proof/*.eca)
PROOF_FILES += $(wildcard proof/*.ec)
PROOF_FILES += $(wildcard proof/big_num_ops/*.ec)
PROOF_FILES += $(wildcard proof/big_num_ops/*.eca)
PROOF_FILES += $(wildcard proof/big_num_ops/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/definition_analysis/*.ec)
PROOF_FILES += $(wildcard proof/definition_analysis/*.eca)
PROOF_FILES += $(wildcard proof/random_bit/*.ec)
PROOF_FILES += $(wildcard proof/random_bit/*.eca)
PROOF_FILES += $(wildcard proof/random_bit/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/*.eca)
PROOF_FILES += $(wildcard proof/rejection_sampling/leakage_freeness/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/leakage_freeness_prhl/*.ec)
PROOF_FILES += $(wildcard proof/rejection_sampling/leakage_freeness_prhl/*.eca)
PROOF_FILES += $(wildcard proof/auxiliary_lemmas/*.ec)
PROOF_FILES += $(wildcard proof/auxiliary_lemmas/*.eca)


JASMIN ?= jasminc
EASYCRYPT ?= easycrypt
ECARGS ?=

EASYCRYPT_REVISION = a214a56
JASMIN_VERSION = 2023.06.1

.DELETE_ON_ERROR :

default : check_all

# Check all EasyCrypt proofs
#check_all : $(PROOF_FILES:.ec{,a}=.eco)
PROOF_OFILES = $(patsubst %.ec,%.eco, $(patsubst %.eca,%.eco, $(PROOF_FILES)))
check_all: $(PROOF_OFILES)

ec_clean:
	echo Removing '.eco' files
	rm -f $(PROOF_OFILES)

# extract_all : $(EXTRACTED_FILES)

%.eco : %.ec $(PROOF_FILES)
	echo Checking "$<"
	$(EASYCRYPT) $(ECARGS) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof/auxiliary_lemmas -I ./proof/big_num_ops -I ./proof/big_num_ops/leakage_freeness  -I ./proof/random_bit -I ./proof/random_bit/leakage_freeness -I ./proof -I Jasmin:./proof/eclib  -I ./proof/jasmin_extracts -I ./proof/rejection_sampling  -timeout "$(TIMEOUT)" "$<"

%.eco : %.eca $(PROOF_FILES)
	echo Checking "$<"
	$(EASYCRYPT) $(ECARGS) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I ./proof/auxiliary_lemmas -I ./proof/big_num_ops -I ./proof/big_num_ops/leakage_freeness  -I ./proof/random_bit -I ./proof/random_bit/leakage_freeness -I ./proof -I Jasmin:./proof/eclib  -I ./proof/jasmin_extracts -I ./proof/rejection_sampling  -timeout "$(TIMEOUT)" "$<"


EXTRACTED_FUNCTIONS = -ec random_bit_naive -ec bn_rsample -ec bn_rsample_i -ec bn_rsample1 -ec random_bit

# extract_all $(EXTRACTED_FILES) : src/bn_rsample.jazz Makefile
# 	$(JASMIN)     $(EXTRACTED_FUNCTIONS) -oec proof/jasmin_extracts/W64_RejectionSamplingExtract.ec  -oecarray proof/jasmin_extracts src/bn_rsample.jazz
# 	$(JASMIN) -CT $(EXTRACTED_FUNCTIONS) -oec proof/jasmin_extracts/W64_RejectionSamplingExtract_ct.ec -oecarray proof/jasmin_extracts src/bn_rsample.jazz


compile_and_run :
	$(info This might take a while...)
	make -C src/example run



