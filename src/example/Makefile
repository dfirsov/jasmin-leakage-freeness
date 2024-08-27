CC ?= gcc
CFLAGS ?= -Wall -Wextra -Wpedantic -Wredundant-decls -Wshadow -Wpointer-arith -O3 -fomit-frame-pointer -z,noexecstack

example : example.c ../bn_rsample.h ../bn_rsample.o
	$(CC) $(CFLAGS) example.c ../bn_rsample.o ./syscalls/randombytes1.c ./syscalls/jasmin_syscall.c -o $@

../bn_rsample.o : $(wildcard ../*.jazz)
	$(MAKE) -C ../ bn_rsample.o

run : example
	./example

clean:
	$(MAKE) -C ../ clean
	rm -f example
