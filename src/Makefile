JASMIN  ?= jasminc

default: bn_rsample.o

bn_rsample.s: $(wildcard *.jazz) 
	$(JASMIN) bn_rsample.jazz -o $@

bn_rsample.o : bn_rsample.s

