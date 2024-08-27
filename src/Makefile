JASMIN  ?= jasminc
JASMIN_FLAGS ?=

default: bn_rsample.o

bn_rsample.s: $(wildcard *.jazz) 
	$(JASMIN) $(JASMIN_FLAGS) bn_rsample.jazz -o $@

bn_rsample.o : bn_rsample.s

clean:
	rm -f bn_rsample.s bn_rsample.o
