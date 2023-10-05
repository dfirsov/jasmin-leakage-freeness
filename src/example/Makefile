
example : example.c ../bn_rsample.h ../bn_rsample.o
	gcc example.c ../bn_rsample.o ./syscalls/randombytes1.c ./syscalls/jasmin_syscall.c -o $@

../bn_rsample.o : $(wildcard ../*.jazz)
	make -C .. bn_rsample.o

run : example
	./example

