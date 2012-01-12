test_ed25519: ../sha512.c ../sha512.h sign.c sign.h test.c lib/*.c lib/*.h lib/*.s lib/*.data
	cd lib; for A in *.c *.s; do gcc -std=c99 -O3 -g0 -Wall -march=native $$A -c -o $$A.o; done
	gcc -std=c99 -O3 -g0 -Wall -march=native ../sha512.c sign.c lib/*.o test.c -o test


