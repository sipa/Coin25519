test_ed25519: sha512.c sha512.h ed25519.c ed25519.h test_ed25519.c ed25519/*.c ed25519/*.h ed25519/*.s ed25519/*.data
	cd ed25519; for A in *.c *.s; do gcc -std=c99 -O3 -g0 -Wall -march=native $$A -c -o $$A.o; done
	gcc -std=c99 -O3 -g0 -Wall -march=native sha512.c ed25519.c ed25519/*.o test_ed25519.c -o test_ed25519


